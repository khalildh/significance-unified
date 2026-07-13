"""Does embedding the WHOLE ontology (one shared frame) change essentiality?

The audit trains a fresh order embedding on each SLICE, so genus concepts and
their differentia fillers sit in a somewhat local coordinate frame — and the
cross-branch fillers that broke the two-scale measure are placed with little
context. A single embedding trained on the FULL ontology puts every concept in
one shared frame: the closest structural approximation to the CCD /
commensurability precondition the essentiality work kept running aground on.

This grades the same slice under both position sources and compares:
  * slice-local  — train on the slice's own nodes (what the audit does now)
  * global       — train once on the full ontology is-a closure, read off
                   positions for the slice entities

Stable numbers ⇒ the finding is robust to embedding scope. A shift ⇒ the
slice-local frame was a confound.

    python src/sigml/embed_scope.py [cl|envo]
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import obo_slice as O  # noqa: E402


def slice_and_defs(o):
    """Replicate obo_slice.main's slice selection (defs + entities + edges)."""
    cands = O.select_defs(o)
    chosen, entities = [], set()
    for c in cands:
        add = c[6] | c[7] | c[8]
        if len(entities | add) > O.MAX_ENTITIES:
            continue
        chosen.append(c)
        entities |= add
        if len(chosen) >= O.MAX_DEFS:
            break
    entities = sorted(entities)
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
            if a in allnodes and t in allnodes:
                edges.add((a, t))
    return chosen, entities, allnodes, edges


def full_ontology_graph(o):
    """All terms + all in-namespace is-a edges (train_positions closes them)."""
    nodes = set(o.name)
    edges = set()
    for c in nodes:
        for p in o.is_a.get(c, []):
            if p in nodes:
                edges.add((c, p))
    return nodes, edges


def tally(chosen, entities, positions_per_seed):
    counts = {"strict": 0, "functional": 0, "fail": 0}
    for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
        grades = [O.grade_definition(entities, sorted(lg), sorted(dm), sorted(lt), raw)
                  for raw in positions_per_seed]
        maj = max(("strict", grades.count("strict")),
                  ("functional", grades.count("functional")),
                  ("fail", grades.count("fail")), key=lambda x: x[1])[0]
        counts[maj] += 1
    return counts


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "cl"
    cfg = O.CONFIGS[name]
    o = O.parse_obo(O.ensure_obo(cfg), cfg["prefix"])
    chosen, entities, allnodes, edges = slice_and_defs(o)
    print(f"=== {cfg['domain']} ===")
    print(f"  slice: {len(chosen)} defs / {len(entities)} entities")

    seeds = O.SEEDS
    local = [O.train_positions(allnodes, edges, s) for s in seeds]
    lt = tally(chosen, entities, local)
    print(f"  slice-local embedding ({len(allnodes)} nodes):  "
          f"strict {lt['strict']}  functional {lt['functional']}  fail {lt['fail']}")

    gnodes, gedges = full_ontology_graph(o)
    print(f"  training global embedding on {len(gnodes)} terms / "
          f"{len(gedges)} is-a edges ...")
    glob = [O.train_positions(gnodes, gedges, s) for s in seeds]
    gt = tally(chosen, entities, glob)
    print(f"  global embedding ({len(gnodes)} nodes):        "
          f"strict {gt['strict']}  functional {gt['functional']}  fail {gt['fail']}")

    ds = gt["strict"] - lt["strict"]
    print(f"\n  strict essentiality: {lt['strict']} (local) → {gt['strict']} (global)"
          f"  Δ={ds:+d}  "
          f"({'stable — robust to scope' if abs(ds) <= max(3, lt['strict'] // 4) else 'MOVED — scope was a confound'})")


if __name__ == "__main__":
    main()
