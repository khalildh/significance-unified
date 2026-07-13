"""What does embedding dimension do to strict essentiality?

Two forces pull opposite ways:
  * higher dim  → more faithful embedding (more room to encode the hierarchy)
  * higher dim  → strict RaiseProd is HARDER (must dominate on every one of the
                  n dimensions), so the strict bar tightens monotonically.

The audits used DIM 6 (kept low so certificates stay `decide`-able). This sweeps
the global embedding over a range of dimensions and, at each, reports embedding
faithfulness plus the essentiality grade distribution — including the robust,
non-degenerate strict count (the only figure that survived the case audit).

    python src/sigml/dim_sweep.py [cl|envo]
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import obo_slice as O  # noqa: E402
from embed_scope import full_ontology_graph, slice_and_defs  # noqa: E402
from repr_quality import closure_edges, energy, auc  # noqa: E402

DIMS = [6, 12, 24, 48]
SEEDS = [0, 1, 2]


def faithfulness(o, gnodes, seed):
    clo = list(closure_edges(o, gnodes))
    rng = np.random.default_rng(seed)
    rng.shuffle(clo)
    sp = int(0.9 * len(clo))
    tr, te = clo[:sp], clo[sp:]
    cset, nl, negs = set(clo), list(gnodes), []
    while len(negs) < len(te):
        a, b = rng.choice(nl), rng.choice(nl)
        if a != b and (a, b) not in cset:
            negs.append((a, b))
    emb = O.train_positions(gnodes, set(tr), seed)
    return auc([energy(emb, c, p) for c, p in te],
               [energy(emb, a, b) for a, b in negs])


def robust_strict(chosen, entities, embs):
    """count definitions strict in a MAJORITY of seeds AND non-degenerate."""
    n = 0
    for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
        units, gmem, dmem = sorted(lt), sorted(lg), sorted(dm)
        s = 0
        deg = False
        for raw in embs:
            pos = {e: tuple(int(round(v * 8)) for v in raw[e]) for e in entities}
            wg = O.diagnostic_weights(pos, gmem, [e for e in entities if e not in gmem])
            wd = O.diagnostic_weights(pos, dmem, [e for e in entities if e not in dmem])
            g = {e: tuple(w * p for w, p in zip(wg, pos[e])) for e in entities}
            d = {e: tuple(w * p for w, p in zip(wd, pos[e])) for e in entities}
            ok = all(all(x <= y for x, y in zip(g[a], d[a])) and g[a] != d[a]
                     for a in units)
            if ok:
                s += 1
                lift = min(sum(1 for x, y in zip(g[a], d[a]) if y > x) for a in units)
                if sum(wg) == 0 or sum(wd) == 0 or lift <= 1:
                    deg = True
        if s > len(embs) // 2 and not deg:
            n += 1
    return n


def grades(chosen, entities, embs):
    tal = {"strict": 0, "functional": 0, "fail": 0}
    for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
        gs = [O.grade_definition(entities, sorted(lg), sorted(dm), sorted(lt), raw)
              for raw in embs]
        maj = max(("strict", gs.count("strict")), ("functional", gs.count("functional")),
                  ("fail", gs.count("fail")), key=lambda x: x[1])[0]
        tal[maj] += 1
    return tal


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "cl"
    cfg = O.CONFIGS[name]
    o = O.parse_obo(O.ensure_obo(cfg), cfg["prefix"])
    chosen, entities, _, _ = slice_and_defs(o)
    gnodes, gedges = full_ontology_graph(o)
    print(f"=== {cfg['domain']}: essentiality vs embedding dimension "
          f"({len(chosen)} defs, global embedding) ===")
    print(f"  {'dim':>4s} {'AUC':>6s} {'strict(plur)':>13s} {'functional':>11s} "
          f"{'neither':>8s} {'strict ROBUST':>14s}")
    for dim in DIMS:
        O.DIM = dim                       # retarget the whole pipeline at this dim
        auc_v = faithfulness(o, gnodes, 0)
        embs = [O.train_positions(gnodes, gedges, s) for s in SEEDS]
        tal = grades(chosen, entities, embs)
        rob = robust_strict(chosen, entities, embs)
        print(f"  {dim:>4d} {auc_v:6.2f} {tal['strict']:>13d} {tal['functional']:>11d} "
              f"{tal['fail']:>8d} {rob:>14d}")


if __name__ == "__main__":
    main()
