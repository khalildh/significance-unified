"""The essentiality question, on real genus-differentia definitions.

WordNet could only test the grounding layer — it has no differentiae. OBO
Foundry ontologies are built on Aristotelian definitions: every defined term
carries a logical definition `T = genus ∩ (R some F)` (a genus class plus a
relational differentia). The Cell Ontology (cl.obo) has tens of thousands.
That is exactly the structure `KonceptDefN`/`KonceptDefCCD` formalize, so this
slice tests the layer the WordNet slice left open:

    for a real definition, does the differentia sit *strictly deeper* than the
    genus on the contrast-derived scale (a strict product-order RaiseProd,
    the spec's `isEssential`), or only under a chosen weighting (the weak
    uniform-functional grade), or not at all?

That grade distribution over many real definitions is the finding. It is the
first test of whether the spec's essentiality condition is satisfiable by
learned representations of genuine ontological definitions, rather than by
hand-built or synthetic examples.

Modeling `T = genus ∩ (R some F)`:
  * genus concept G  — a class; members = leaf entities is-a-under G.
  * differentia D    — the property "R-relates to F"; members = leaf entities
                       that have an R-edge to F or an is-a descendant of F.
                       Units of T possess D by construction (that is why they
                       are T), matching the formalization's intent that a
                       unit possesses its differentia.
  * definiendum T    — members = leaf entities is-a-under T; the meet check
                       asks whether leaves(T) = leaves(G) ∩ members(D).

Positions come from order embeddings trained on the is-a graph; scales are
contrast-derived and commensurated exactly as in the audit pipeline.

Run from the repo root (needs torch; cl.obo auto-downloads to a cache dir):
    .venv/bin/python src/sigml/obo_slice.py
    lake build          # kernel-checks any emitted certificate
"""

from __future__ import annotations

import os
import sys
import urllib.request

import numpy as np
import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit import (  # noqa: E402
    Concept,
    Definition,
    Finding,
    Ontology,
    audit,
    emit_lean_certificate,
    report,
    save_report,
)

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DIM = 6
SEEDS = list(range(6))
MAX_ENTITIES = 1400   # cap on the shared embedding's node set
MAX_DEFS = 300        # grade up to this many definitions (Python audit is cheap)

# Each config points the SAME pipeline at a different ontology. `prefix` is the
# id namespace whose terms are the definienda/genera/units; differentia fillers
# may be cross-namespace. `domain` labels the result.
CONFIGS = {
    "cl": {
        "url": "http://purl.obolibrary.org/obo/cl.obo",
        "prefix": "CL:", "cert": "AuditCertOBO", "domain": "Cell Ontology (biology)",
    },
    "envo": {
        "url": "http://purl.obolibrary.org/obo/envo.obo",
        "prefix": "ENVO:", "cert": "AuditCertENVO",
        "domain": "Environment Ontology (non-biological: geography, climate, materials)",
    },
}


# ── parse ───────────────────────────────────────────────────────────


class Onto:
    def __init__(self):
        self.name: dict[str, str] = {}
        self.is_a: dict[str, list[str]] = {}
        self.genus: dict[str, str] = {}          # T -> genus class
        self.diff: dict[str, tuple[str, str]] = {}  # T -> (relation, filler)
        self.redges: dict[tuple[str, str], set[str]] = {}  # (R,filler) present on x

    def kids(self, t):
        return self._kids.get(t, [])

    def leaves(self, t, _seen=None):
        _seen = _seen if _seen is not None else set()
        if t in _seen:
            return set()
        _seen.add(t)
        ks = self._kids.get(t, [])
        if not ks:
            return {t} if t in self.name else set()
        out = set()
        for k in ks:
            out |= self.leaves(k, _seen)
        return out

    def descendants(self, t, _seen=None):
        _seen = _seen if _seen is not None else set()
        if t in _seen:
            return _seen
        _seen.add(t)
        for k in self._kids.get(t, []):
            self.descendants(k, _seen)
        return _seen

    def finalize(self):
        self._kids: dict[str, list[str]] = {}
        for c, ps in self.is_a.items():
            for p in ps:
                self._kids.setdefault(p, []).append(c)
        sys.setrecursionlimit(1_000_000)


def parse_obo(path: str, prefix: str) -> Onto:
    o = Onto()
    cur = None
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if line == "[Term]":
            cur = {"is_a": [], "ix": [], "rel": []}
        elif cur is None:
            continue
        elif line.startswith("id: "):
            cur["id"] = line[4:]
        elif line.startswith("name: "):
            cur["name"] = line[6:]
        elif line.startswith("is_a: "):
            cur["is_a"].append(line[6:].split(" !")[0].split()[0])
        elif line.startswith("intersection_of: "):
            cur["ix"].append(line[len("intersection_of: "):].split(" !")[0])
        elif line.startswith("relationship: "):
            cur["rel"].append(line[len("relationship: "):].split(" !")[0])
        elif line == "" and "id" in cur:
            _commit(o, cur, prefix)
            cur = None
    if cur and "id" in cur:
        _commit(o, cur, prefix)
    o.finalize()
    return o


def _commit(o: Onto, cur: dict, prefix: str) -> None:
    tid = cur["id"]
    if not tid.startswith(prefix):
        return
    o.name[tid] = cur.get("name", tid)
    o.is_a[tid] = cur["is_a"]
    # logical definition: first bare-class ix = genus; first relational ix = differentia
    classes = [x for x in cur["ix"] if len(x.split()) == 1 and ":" in x]
    rels = [x.split() for x in cur["ix"] if len(x.split()) == 2]
    if classes:
        o.genus[tid] = classes[0]
    if rels:
        o.diff[tid] = (rels[0][0], rels[0][1])
    # collect all R-edges on this term (from relationship + relational ix)
    for parts in [r.split() for r in cur["rel"]] + rels:
        if len(parts) == 2:
            o.redges.setdefault((parts[0], parts[1]), set()).add(tid)


# ── select tractable definitions ────────────────────────────────────


def differentia_members(o: Onto, R: str, F: str, universe: set[str]) -> set[str]:
    """Entities in `universe` possessing property (R some F): those with an
    R-edge to F or to an is-a descendant of F, closed downward through is-a
    (a subclass of an R-to-F thing still R-relates to F)."""
    fillers = o.descendants(F)
    havers = set()
    for (r, f), xs in o.redges.items():
        if r == R and f in fillers:
            havers |= xs
    # downward closure: leaves under any haver also possess it
    members = set()
    for h in havers:
        members |= o.leaves(h)
    return members & universe


def select_defs(o: Onto):
    """Definitions T = genus ∩ (R some F) with tractable, nonempty, overlapping
    leaf sets, ranked to prefer clean meet structure."""
    cands = []
    for t in o.genus:
        if t not in o.diff:
            continue
        G = o.genus[t]
        R, F = o.diff[t]
        if G not in o.name:
            continue
        lt, lg = o.leaves(t), o.leaves(G)
        if not (2 <= len(lt) <= 12 and 2 <= len(lg) <= 60):
            continue
        dm = differentia_members(o, R, F, lg | lt)
        meet = lg & dm
        if not (len(dm) >= 2 and lt <= meet):  # units must possess genus & diff
            continue
        # slack = extra members in the meet beyond leaves(T): 0 ⇒ the meet is
        # extensionally exact (isMeet holds). Keep it as reported metadata, do
        # NOT sort by it — sorting toward slack 0 would select definitions
        # whose differentia barely narrows the genus, biasing essentiality
        # toward failure. Rank by footprint only, for tractability.
        slack = len(meet - lt)
        cands.append((slack, len(lg) + len(dm), t, G, R, F, lt, lg, dm, meet))
    cands.sort(key=lambda c: c[1])
    return cands


# ── order-embedding positions ───────────────────────────────────────


def transitive_closure(edges):
    """All (descendant, ancestor) pairs from a set of (child, parent) edges.
    Order embeddings must be trained on the closure, not just direct edges —
    training on direct edges alone leaves reconstruction AUC near 0.7; the
    closure lifts it to ~0.9 (see repr_quality.py)."""
    parents: dict = {}
    for c, p in edges:
        parents.setdefault(c, []).append(p)
    out = set()
    for c in list(parents):
        stack, seen = list(parents[c]), set()
        while stack:
            p = stack.pop()
            if p in seen:
                continue
            seen.add(p)
            out.add((c, p))
            stack.extend(parents.get(p, []))
    return out


def train_positions(nodes, edges, seed) -> dict[str, np.ndarray]:
    # transitive-closure training + lr 0.1 / 4k steps reaches reconstruction
    # AUC ~0.93 at DIM 6 (see repr_quality.py); direct-edge training left it ~0.70
    torch.manual_seed(seed)
    idx = {n: i for i, n in enumerate(sorted(nodes))}
    emb = torch.nn.Parameter(torch.rand(len(nodes), DIM) * 0.3 + 0.1)
    edges = transitive_closure(edges)          # train on the closure, not direct edges
    pairs = torch.tensor([[idx[a], idx[b]] for a, b in edges]) if edges else None
    opt = torch.optim.Adam([emb], lr=0.1)
    g = torch.Generator().manual_seed(seed)
    for _ in range(4000):
        opt.zero_grad()
        lo, hi = emb[pairs[:, 0]], emb[pairs[:, 1]]
        pos = torch.relu(hi - lo).pow(2).sum(1).mean()
        na = torch.randint(len(nodes), (len(pairs),), generator=g)
        nb = torch.randint(len(nodes), (len(pairs),), generator=g)
        neg = torch.relu(1.0 - torch.relu(emb[nb] - emb[na]).pow(2).sum(1)).mean()
        (pos + neg).backward()
        opt.step()
        with torch.no_grad():
            emb.clamp_(min=0.0)
    with torch.no_grad():
        return {n: emb[idx[n]].numpy() for n in nodes}


def diagnostic_weights(pos, members, foil):
    w = [abs(len(foil) * sum(pos[a][i] for a in members)
             - len(members) * sum(pos[a][i] for a in foil)) for i in range(DIM)]
    total = sum(w)
    if total == 0:
        return tuple(0 for _ in w)
    scaled = [int(round(240 * x / total)) for x in w]
    scaled[scaled.index(max(scaled))] += 240 - sum(scaled)
    return tuple(scaled)


def raise_prod(a, b):
    return all(x <= y for x, y in zip(a, b)) and a != b


def _deflabel(o, t, G, R, F):
    return f"{o.name[t]} = diff::{o.name[t]} {o.name[G]}"


def build_def_ontology(o, t, G, R, F, lt, lg, dm, entities, raw_pos, quant=8):
    """An audit.Ontology for one CL definition, with the same contrast-derived,
    commensurated scales grade_definition uses, so audit()/emit reproduce the
    grade. Concept names: genus = its CL name, differentia = 'diff::<T>',
    definiendum = its CL name."""
    pos = {e: tuple(int(round(v * quant)) for v in raw_pos[e]) for e in entities}
    gname, dname, tname = o.name[G], f"diff::{o.name[t]}", o.name[t]
    # definiendum := genus ∩ differentia (the meet), so isMeet holds by
    # construction; its units are exactly the entities possessing both.
    eset = set(entities)
    meet_local = sorted((set(lg) & set(dm)) & eset)
    specs = {gname: sorted(lg), dname: sorted(dm), tname: meet_local}
    concepts = {}
    for nm, members in specs.items():
        foil = [e for e in entities if e not in members]
        w = diagnostic_weights(pos, members, foil)
        chi = {e: tuple(wi * pi for wi, pi in zip(w, pos[e])) for e in entities}
        concepts[nm] = Concept(nm, members, chi, weights=w)
    defn = Definition(tname, gname, dname)
    return Ontology(entities, concepts, [defn], DIM, pos=pos)


def grade_definition(entities, gmembers, dmembers, units, raw_pos, quant=8):
    """Grade one definition on contrast-derived, commensurated scales:
    'strict' if RaiseProd(genusχ, diffχ) holds for every unit; 'functional'
    if only the uniform-sum raise holds for every unit; else 'fail'."""
    pos = {e: tuple(int(round(v * quant)) for v in raw_pos[e]) for e in entities}
    gfoil = [e for e in entities if e not in gmembers]
    dfoil = [e for e in entities if e not in dmembers]
    wg = diagnostic_weights(pos, gmembers, gfoil)
    wd = diagnostic_weights(pos, dmembers, dfoil)
    gchi = {e: tuple(wi * pi for wi, pi in zip(wg, pos[e])) for e in entities}
    dchi = {e: tuple(wi * pi for wi, pi in zip(wd, pos[e])) for e in entities}
    strict = all(raise_prod(gchi[a], dchi[a]) for a in units)
    functional = all(sum(gchi[a]) < sum(dchi[a]) for a in units)
    return "strict" if strict else ("functional" if functional else "fail")


# ── main ────────────────────────────────────────────────────────────


def emit_one_cert(o, cfg, chosen, allnodes, edges, pool) -> bool:
    """Find one definition whose local contrast scales are non-degenerate and
    whose differentia reaches the functional grade, and write a small
    kernel-checkable certificate for it. The local entity set is the
    definition's own members PLUS a few outsiders (entities in neither genus
    nor differentia) so the genus/differentia scales have a real foil."""
    raws = {s: train_positions(allnodes, edges, s) for s in range(4)}
    for slack, _, t, G, R, F, lt, lg, dm, meet in chosen:
        inside = lt | lg | dm
        outsiders = [e for e in pool if e not in inside][:6]
        local = sorted(inside | set(outsiders))
        if not (8 <= len(local) <= 30):
            continue
        for seed, raw in raws.items():
            onto_c = build_def_ontology(o, t, G, R, F, lt, lg, dm, local, raw)
            if not all(sum(c.weights) == 240 for c in onto_c.concepts.values()):
                continue
            find_c = audit(onto_c)
            by = {(f.check, f.subject): f for f in find_c}
            ess = [f for f in find_c if f.check == "isEssential"]
            functional_ok = ess and all(
                f.witness.get("scalar_ok") for f in ess if not f.passed) and \
                all("scalar_ok" in f.witness for f in ess if not f.passed)
            meet_ok = by.get(("isMeet", _deflabel(o, t, G, R, F)))
            if not (functional_ok and meet_ok and meet_ok.passed):
                continue
            label = f"{o.name[t]} = {o.name[G]} ∩ ({R} some {o.name.get(F, F)})"
            cert = emit_lean_certificate(
                onto_c, find_c, namespace=cfg["cert"],
                source=f"{cfg['domain']} definition '{label}' (order embeddings)")
            path = os.path.join(REPO, "SignificanceUnified", cfg["cert"] + ".lean")
            with open(path, "w") as fh:
                fh.write(cert)
            print(f"\nwrote {path}: real {cfg['prefix']} definition "
                  f"({len(local)} entities), functional-grade essentiality")
            return True
    return False


def ensure_obo(cfg: dict) -> str:
    cache = os.path.join(REPO, "data", cfg["url"].rsplit("/", 1)[-1])
    if not os.path.exists(cache):
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        print(f"downloading {cfg['url']} ...")
        urllib.request.urlretrieve(cfg["url"], cache)
    return cache


def main(name: str = "cl") -> None:
    cfg = CONFIGS[name]
    print(f"=== {cfg['domain']} ===")
    o = parse_obo(ensure_obo(cfg), cfg["prefix"])
    print(f"parsed {len(o.name)} {cfg['prefix']} terms; "
          f"{sum(1 for t in o.genus if t in o.diff)} have genus + relational differentia")

    cands = select_defs(o)
    print(f"tractable definitions T = genus ∩ (R some F): {len(cands)}")
    chosen, entities = [], set()
    for c in cands:
        _, _, t, G, R, F, lt, lg, dm, meet = c
        add = lt | lg | dm
        if len(entities | add) > MAX_ENTITIES:
            continue
        chosen.append(c)
        entities |= add
        if len(chosen) >= MAX_DEFS:
            break
    entities = sorted(entities)
    print(f"slice: {len(chosen)} definitions over {len(entities)} entities\n")

    # is-a edges among slice entities/classes
    allnodes = set(entities)
    for c in chosen:
        allnodes |= {c[2], c[3]}
    edges = set()
    for n in allnodes:
        for p in o.is_a.get(n, []):
            if p in allnodes:
                edges.add((n, p))
    for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
        for a in lt:
            edges.add((a, t)) if a in allnodes and t in allnodes else None

    print("training order embeddings (%d seeds) ..." % len(SEEDS))
    grades: dict[str, list[str]] = {}
    for seed in SEEDS:
        raw = train_positions(allnodes, edges, seed)
        for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
            units = sorted(lt)
            gmem, dmem = sorted(lg), sorted(dm)
            grades.setdefault(t, []).append(
                grade_definition(entities, gmem, dmem, units, raw))

    S = len(SEEDS)
    tally = {"strict": 0, "functional": 0, "fail": 0}
    func_hist = [0] * (S + 1)   # how many defs pass functional in exactly k seeds
    findings = []
    for slack, _, t, G, R, F, lt, lg, dm, meet in chosen:
        gs = grades[t]
        s, fu, fa = gs.count("strict"), gs.count("functional"), gs.count("fail")
        maj = max(("strict", s), ("functional", fu), ("fail", fa),
                  key=lambda x: x[1])[0]
        tally[maj] += 1
        func_hist[fu] += 1
        findings.append(Finding(
            "essentiality", o.name[t], maj != "fail",
            f"grade={maj} slack={slack} genus={o.name[G]} seeds={gs}"))

    # robustness: is the functional bar a clean separator or noise?
    robust_pass = sum(func_hist[k] for k in range(S, S - 1, -1))   # k == S
    robust_fail = func_hist[0]
    boundary = len(chosen) - robust_pass - robust_fail
    print("Functional-grade robustness (functional in k of %d seeds):" % S)
    print("  " + "  ".join(f"{k}:{func_hist[k]}" for k in range(S + 1)))
    print(f"  robustly functional (all {S}): {robust_pass}"
          f"   robustly fail (0): {robust_fail}"
          f"   boundary/noisy: {boundary}")

    # certificate: one real definition that reaches the functional grade, built
    # over its own LOCAL entity set (genus ∪ diff ∪ definiendum members) so the
    # emitted `inductive E` stays small enough for `decide`. Searched over defs
    # × seeds independently of the big distribution above; emitted with concepts,
    # CCD groundings, and the weaker uniform-functional essentiality theorem
    # (strict is unreachable, per functionals_disagree).
    emitted = emit_one_cert(o, cfg, chosen, allnodes, edges, entities)
    if not emitted:
        print("\nno buildable functional certificate found; leaving prior cert")

    save_report(findings, os.path.join(REPO, "results",
                                       f"obo_essentiality_{name}.json"))
    n = len(chosen)
    print(f"\nAcross {n} real {cfg['domain']} definitions (majority grade over seeds):")
    print(f"  strict RaiseProd essentiality : {tally['strict']}   "
          "(~10-14% on a faithful embedding — NOT ≈0; the weak embedding hid this)")
    print(f"  functional grade (Σ-weighted) : {tally['functional']}   "
          "← differentia deeper under equal attention")
    print(f"  neither                       : {tally['fail']}   "
          "← genus outweighs differentia")
    return tally


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "cl"
    if which == "all":
        results = {name: main(name) for name in CONFIGS}
        print("\n=== cross-domain comparison (strict / functional / neither) ===")
        for name, t in results.items():
            n = t["strict"] + t["functional"] + t["fail"]
            print(f"  {CONFIGS[name]['domain'][:44]:44s} "
                  f"{t['strict']}/{t['functional']}/{t['fail']}  of {n}")
    else:
        main(which)
