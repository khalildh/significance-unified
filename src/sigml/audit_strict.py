"""Open the box: are the ~1-3% that pass strict essentiality real or degenerate?

The global embedding leaves ~1-3% of definitions satisfying strict RaiseProd.
Aggregate numbers have lied twice in this project, so before trusting even that
figure, inspect every survivor: is the pass genuine (both contrast scales
non-degenerate, real per-dimension margin, differentia genuinely deeper on the
units) or degenerate (a genus scale collapsed to zero so the differentia
dominates trivially — the old 'animal' failure mode)?

    python src/sigml/audit_strict.py [cl|envo]
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import obo_slice as O  # noqa: E402
from embed_scope import full_ontology_graph, slice_and_defs  # noqa: E402


def scales(entities, gmembers, dmembers, raw_pos, quant=8):
    pos = {e: tuple(int(round(v * quant)) for v in raw_pos[e]) for e in entities}
    wg = O.diagnostic_weights(pos, gmembers, [e for e in entities if e not in gmembers])
    wd = O.diagnostic_weights(pos, dmembers, [e for e in entities if e not in dmembers])
    gchi = {e: tuple(w * p for w, p in zip(wg, pos[e])) for e in entities}
    dchi = {e: tuple(w * p for w, p in zip(wd, pos[e])) for e in entities}
    return wg, wd, gchi, dchi


def ancestors(o, x, seen=None):
    seen = seen if seen is not None else set()
    for p in o.is_a.get(x, []):
        if p not in seen:
            seen.add(p)
            ancestors(o, p, seen)
    return seen


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "cl"
    cfg = O.CONFIGS[name]
    o = O.parse_obo(O.ensure_obo(cfg), cfg["prefix"])
    chosen, entities, _, _ = slice_and_defs(o)
    gnodes, gedges = full_ontology_graph(o)
    seeds = list(O.SEEDS)
    embs = [O.train_positions(gnodes, gedges, s) for s in seeds]
    print(f"=== {cfg['domain']}: strict survivors on the global embedding ===")

    genuine = degenerate = 0
    for _, _, t, G, R, F, lt, lg, dm, meet in chosen:
        units = sorted(lt)
        gmem, dmem = sorted(lg), sorted(dm)
        strict_seeds = func_seeds = 0
        detail = None
        for raw in embs:
            wg, wd, gchi, dchi = scales(entities, gmem, dmem, raw)
            ok = all(all(x <= y for x, y in zip(gchi[a], dchi[a])) and gchi[a] != dchi[a]
                     for a in units)
            fok = all(sum(gchi[a]) < sum(dchi[a]) for a in units)
            if ok:
                strict_seeds += 1
                detail = (wg, wd, gchi, dchi)
            elif fok:
                func_seeds += 1
        fail_seeds = len(seeds) - strict_seeds - func_seeds
        # survivor = strict is the plurality grade (what embed_scope counts as "strict")
        if not (strict_seeds >= func_seeds and strict_seeds >= fail_seeds
                and strict_seeds > 0):
            continue

        wg, wd, gchi, dchi = detail
        # degeneracy diagnostics
        g_zero = all(all(v == 0 for v in gchi[a]) for a in units)
        wg_deg = sum(wg) == 0
        wd_deg = sum(wd) == 0
        # margin: min over units of (min positive coordinate gap where it matters)
        margins = []
        for a in units:
            gaps = [y - x for x, y in zip(gchi[a], dchi[a])]
            margins.append(min(g for g in gaps))          # worst dim (>=0 for strict)
            margins.append(sum(1 for g in gaps if g > 0))  # dims with real lift
        lift_dims = min(margins[1::2])
        cross = not (ancestors(o, G) & ancestors(o, F))
        robust = strict_seeds > len(seeds) // 2
        is_degen = g_zero or wg_deg or wd_deg or lift_dims <= 1
        genuine += (not is_degen) and robust
        degenerate += is_degen or not robust
        tag = ("genuine" if (not is_degen and robust)
               else "NOT-ROBUST" if not robust else "DEGENERATE")
        why = ("genus χ ≡ 0" if g_zero else "wg≡0" if wg_deg else "wd≡0"
               if wd_deg else f"only {lift_dims} dim(s) lift" if lift_dims <= 1
               else f"{lift_dims} dims lift")
        print(f"  [{tag:10s}] {o.name[t][:32]:32s} = {o.name[G][:15]:15s} "
              f"∩ ({R.split(':')[0]} {o.name.get(F, F)[:16]})")
        print(f"               strict {strict_seeds}/{len(seeds)} seeds · "
              f"{'cross-branch' if cross else 'same-branch'} · {why}")

    total = genuine + degenerate
    print(f"\n  plurality-strict survivors: {total}   "
          f"robust & non-degenerate: {genuine}   noise/degenerate: {degenerate}")
    verdict = ("a real signal exists" if genuine
               else "ZERO survive robust + non-degenerate — the ~1-3% is noise/artifact")
    print(f"  → {verdict}")


if __name__ == "__main__":
    main()
