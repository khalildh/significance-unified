"""First real-data slice: audit a WordNet Carnivora subtree against the spec.

WordNet gives hypernymy (is-a) and nothing else, so this slice tests the
*grounding layer* of the formalization — CCD₃ clustering, the subsumption
preorder, acyclicity — on real lexical structure. It does NOT test
essentiality: WordNet has no differentiae. (The subtree is chosen on
purpose: the repository's toy example is dog/wolf/cat, and Carnivora is the
real version — Canidae vs Felidae vs Ursidae vs Mustelidae vs Procyonidae.)

Two position sources are run and cross-tabulated, because a CCD₃ failure has
two possible causes and they must be told apart:

  * TRAINED — Vendrov-style order embeddings (torch) fit to the hypernym
    edges. The honest "learned representation" story; a failure here might be
    the embedding, not the concept.
  * GEOMETRIC — deterministic landmark-distance coordinates: each entity's
    proximity to each family root. Reproducible, no training. A reference in
    which the taxonomy's own structure is respected by construction.

A concept that fails to ground under BOTH sources fails for structural
reasons (its members do not cohere against outsiders in the lexical
hierarchy at all). A concept that grounds under GEOMETRIC but fails under
TRAINED failed because the embedding did not capture it. That cross-tab is
the actual finding; a single audit could not separate the two.

Run from the repo root:
    .venv/bin/python src/sigml/wordnet_slice.py
    lake build          # kernel-checks the curated-core certificate
"""

from __future__ import annotations

import os
import sys

import numpy as np
import torch
import nltk

try:
    nltk.data.find("corpora/wordnet.zip")
except LookupError:
    nltk.download("wordnet", quiet=True)
from nltk.corpus import wordnet as wn  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit import (  # noqa: E402
    Concept,
    Ontology,
    audit,
    emit_lean_certificate,
    report,
    save_report,
)

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DIM = 5
CAP = 10  # max members per family; excess is logged, never silently dropped
SEED = 11

FAMILIES = [
    "canine.n.02",
    "feline.n.01",
    "bear.n.01",
    "musteline_mammal.n.01",
    "procyonid.n.01",
]



# ── slice extraction ────────────────────────────────────────────────


DROP = {"bitch", "bear_cub", "bruin", "vixen", "reynard", "puppy",
        "wolf_pup", "brood_bitch", "toy_dog", "working_dog", "hunting_dog"}


def _species_frontier(fam: str) -> list[str]:
    """Members of a family at genus/species granularity. Use the family's
    direct hyponyms when there are enough of them (they are the natural
    genera — dog, wolf, fox, jackal…); only expand one level for thin
    families (feline = cat, big_cat → cat, lion, tiger…) so we do not drill
    into dog *breeds*. Deterministic (WordNet order)."""
    s = wn.synset(fam)
    direct = sorted(s.hyponyms(), key=lambda x: x.name())
    if len(direct) >= 4:
        names = [h.name() for h in direct]
    else:
        names = []
        for h in direct:
            kids = sorted(h.hyponyms(), key=lambda x: x.name())
            names.extend(k.name() for k in kids) if kids else names.append(h.name())
    seen, out = set(), []
    for name in names:
        if name.split(".")[0] in DROP or name in seen:
            continue
        seen.add(name)
        out.append(name)
    return out


def build_slice() -> tuple[list[str], dict[str, list[str]]]:
    concepts: dict[str, list[str]] = {}
    for fam in FAMILIES:
        members = _species_frontier(fam)
        if len(members) > CAP:
            print(f"  {fam}: {len(members)} members, capping to {CAP} "
                  f"(dropped {[m.split('.')[0] for m in members[CAP:]]})")
            members = members[:CAP]
        concepts[fam] = members
    entities = sorted({e for ms in concepts.values() for e in ms})
    return entities, concepts


def hypernym_edges(entities: list[str], concepts: dict[str, list[str]]):
    """is-a edges among {entities ∪ families ∪ carnivore}, from WordNet."""
    nodes = set(entities) | set(FAMILIES) | {"carnivore.n.01"}
    edges = set()
    for name in nodes:
        s = wn.synset(name)
        for hyper in s.hypernyms():
            if hyper.name() in nodes:
                edges.add((name, hyper.name()))
    # ensure every member links to its family even across skipped levels
    for fam, members in concepts.items():
        for m in members:
            edges.add((m, fam))
        edges.add((fam, "carnivore.n.01"))
    return nodes, edges


# ── position source 1: trained order embeddings ─────────────────────


def train_positions(nodes, edges, seed=SEED) -> dict[str, np.ndarray]:
    torch.manual_seed(seed)
    idx = {n: i for i, n in enumerate(sorted(nodes))}
    emb = torch.nn.Parameter(torch.rand(len(nodes), DIM) * 0.5 + 0.1)
    pos_pairs = torch.tensor([[idx[a], idx[b]] for a, b in edges])
    opt = torch.optim.Adam([emb], lr=0.05)
    allnodes = list(range(len(nodes)))
    g = torch.Generator().manual_seed(SEED)
    for _ in range(1500):
        opt.zero_grad()
        lo, hi = emb[pos_pairs[:, 0]], emb[pos_pairs[:, 1]]
        # order-embedding energy: hyponym should dominate hypernym
        pos_energy = torch.relu(hi - lo).pow(2).sum(1).mean()
        na = torch.randint(len(nodes), (len(pos_pairs),), generator=g)
        nb = torch.randint(len(nodes), (len(pos_pairs),), generator=g)
        neg_energy = torch.relu(1.0 - torch.relu(emb[nb] - emb[na]).pow(2).sum(1)).mean()
        (pos_energy + neg_energy).backward()
        opt.step()
        with torch.no_grad():
            emb.clamp_(min=0.0)
    with torch.no_grad():
        return {n: emb[idx[n]].numpy() for n in nodes}


# ── position source 2: deterministic landmark geometry ──────────────


def geometric_positions(nodes, edges) -> dict[str, np.ndarray]:
    """Deterministic per-synset structural features (no training). Five
    intrinsic graph statistics that vary between siblings, so the control has
    within-family resolution:

        [min depth from root, #direct hyponyms, log subtree size,
         #lemmas (synonyms), distance to carnivore root]

    A pure landmark-distance embedding was tried first and collapses every
    sibling to one point — the is-a hierarchy is symmetric under sibling
    exchange, so bare structure gives no within-family discrimination at all.
    That collapse is itself a finding (reported separately); these intrinsic
    features are the fair control that avoids it."""
    adj: dict[str, set[str]] = {n: set() for n in nodes}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    def dist_to(src: str, dst: str) -> int:
        seen, frontier, d = {src}, [src], 0
        while frontier:
            if dst in frontier:
                return d
            d += 1
            frontier = [v for u in frontier for v in adj[u] if v not in seen
                        and not seen.add(v)]
        return 99

    out = {}
    for n in nodes:
        s = wn.synset(n)
        subtree = len(list(s.closure(lambda x: x.hyponyms())))
        out[n] = np.array([
            float(s.min_depth()),
            float(len(s.hyponyms())),
            float(np.log1p(subtree)),
            float(len(s.lemmas())),
            float(dist_to(n, "carnivore.n.01")),
        ])
    return out


# ── build an Ontology (audit.py types) from a position source ───────


def diagnostic_weights(pos, members, foil):
    w = [
        abs(len(foil) * sum(pos[a][i] for a in members)
            - len(members) * sum(pos[a][i] for a in foil))
        for i in range(DIM)
    ]
    total = sum(w)
    if total == 0:
        return tuple(0 for _ in w)
    scaled = [int(round(240 * x / total)) for x in w]
    scaled[scaled.index(max(scaled))] += 240 - sum(scaled)
    return tuple(scaled)


def make_ontology(entities, concepts, raw_pos, quant=8) -> Ontology:
    pos = {e: tuple(int(round(v * quant)) for v in raw_pos[e]) for e in entities}
    cs = {}
    for fam, members in concepts.items():
        foil = [e for e in entities if e not in members]
        w = diagnostic_weights(pos, members, foil)
        chi = {e: tuple(wi * pi for wi, pi in zip(w, pos[e])) for e in entities}
        cs[fam] = Concept(fam, list(members), chi, weights=w)
    return Ontology(entities, cs, [], DIM, pos=pos)


def ccd3_pass_rate(findings, subject) -> tuple[int, int]:
    fs = [f for f in findings if f.check == "ccd3" and f.subject == subject]
    return sum(f.passed for f in fs), len(fs)


# ── main ────────────────────────────────────────────────────────────


SEEDS = list(range(8))


def main() -> None:
    print("extracting Carnivora slice ...")
    entities, concepts = build_slice()
    print(f"  {len(entities)} entities across {len(concepts)} families")
    for fam, ms in concepts.items():
        print(f"    {fam.split('.')[0]:20s} {[m.split('.')[0] for m in ms]}")
    nodes, edges = hypernym_edges(entities, concepts)

    # deterministic structural control (one pass)
    geometric = geometric_positions(nodes, edges)
    find_g = audit(make_ontology(entities, concepts, geometric))
    save_report(find_g, os.path.join(REPO, "results", "wordnet_audit_geometric.json"))

    # trained order embeddings across many seeds → mean ± range per family
    print(f"training order embeddings ({len(SEEDS)} seeds) ...")
    trained_rates: dict[str, list[float]] = {fam: [] for fam in concepts}
    trained0 = None
    for si, seed in enumerate(SEEDS):
        trained = train_positions(nodes, edges, seed=seed)
        if si == 0:
            trained0 = trained
        find = audit(make_ontology(entities, concepts, trained))
        if si == 0:
            save_report(find, os.path.join(REPO, "results",
                                           "wordnet_audit_trained.json"))
        for fam in concepts:
            p, n = ccd3_pass_rate(find, fam)
            if n:
                trained_rates[fam].append(p / n)

    print("\nCCD₃ grounding by family — trained (mean [min,max] over seeds) "
          "vs geometric control:")
    print(f"  {'family':20s} {'trained':>20s} {'geom':>7s}   reading")
    for fam in concepts:
        rs = trained_rates[fam]
        _, ng = ccd3_pass_rate(find_g, fam)
        pg, _ = ccd3_pass_rate(find_g, fam)
        rg = pg / ng if ng else 0.0
        if ng <= 1 or not rs:
            print(f"  {fam.split('.')[0]:20s} {'underpopulated':>20s}")
            continue
        mean, lo, hi = sum(rs) / len(rs), min(rs), max(rs)
        # agreement between two independent sources ⇒ about the taxonomy
        if mean >= 0.9 and rg >= 0.9:
            reading = "grounds under both — structural"
        elif abs(mean - rg) <= 0.15:
            reading = f"partial under both (~{round(50 * (mean + rg))}%) — structural"
        elif mean - rg > 0.15:
            reading = "trained-only — embedding captures it"
        else:
            reading = "geometric-only — training underfits"
        band = f"{mean:.2f} [{lo:.2f},{hi:.2f}]"
        print(f"  {fam.split('.')[0]:20s} {band:>20s} {rg:6.2f}   {reading}")
    trained = trained0

    # curated-core certificate from ACTUAL slice members (guaranteed present):
    # a two-family dog/wolf/fox vs cat/lion/tiger core, the WordNet-sourced
    # version of the repository's running example. Kept small so `decide`
    # closes the emitted similarity proofs.
    # the dog·wolf / lion·tiger core — WordNet's version of the repository's
    # running example, prototypical members chosen for a clean demonstration
    # certificate (not a representative sample: grounding is what certifies)
    def pick(fam, lemmas):
        present = [m for m in concepts[fam] if m.split(".")[0] in lemmas]
        return present[:2] if len(present) >= 2 else concepts[fam][:2]
    core = {
        "canine.n.02": pick("canine.n.02", {"dog", "wolf"}),
        "feline.n.01": pick("feline.n.01", {"lion", "tiger"}),
    }
    core_entities = sorted({e for ms in core.values() for e in ms})
    for label, raw in (("trained", trained), ("geometric", geometric)):
        onto_c = make_ontology(core_entities, core, raw)
        find_c = audit(onto_c)
        ccd = [f for f in find_c if f.check == "ccd3"]
        grounded = sum(f.passed for f in ccd)
        print(f"\ncurated core ({label}): {grounded}/{len(ccd)} CCD₃ pairs grounded "
              f"({', '.join(m.split('.')[0] for m in core_entities)})")
        if all(f.passed for f in ccd):
            cert = emit_lean_certificate(
                onto_c, find_c, namespace="AuditCertWordNet",
                source=f"WordNet Carnivora ({label} order embeddings)")
            path = os.path.join(REPO, "SignificanceUnified", "AuditCertWordNet.lean")
            with open(path, "w") as fh:
                fh.write(cert)
            print(f"  wrote {path} ({label} positions) — run `lake build` to check")
            return
    print("\ncurated core did not fully ground under either source; no cert emitted")


if __name__ == "__main__":
    main()
