"""Two independent scales: subsumption (width) vs relation (depth).

The earlier OBO slices collapsed everything onto one contrast-derived χ and
found the essentiality signal was near-random. That collapse was the mistake.
The formalization's own **Definition Diamond** (`preorder_not_partial_order`,
"category vs depth scale independence") says a concept lives on TWO independent
axes:

  * subsumption / category  — wider vs specific.   From is-a.
  * depth / significance     — abstraction vs concrete.  NOT from is-a.

Aristotelian essentiality is the claim that these two axes *invert* for a
definition `T = genus ∩ (R some F)`: the genus is the WIDER concept (high on
subsumption) while the differentia is the DEEPER one (high on the significance
axis). A single is-a-trained scale cannot see this — is-a only gives the width
axis, so the depth axis has to come from the RELATIONS (the reason training on
is-a alone could never test essentiality).

This probe measures both axes explicitly, deterministically (no seeds, no
commensuration coin-flip), and asks three well-posed questions:

  Q1. Are the two axes actually independent in real ontologies (the Diamond),
      or does relational depth just track subsumption width?
  Q2. Do real genus-differentia definitions show the inversion — genus wider on
      subsumption, differentia deeper on the relational axis?
  Q3. Is that inversion *systematic* (most definitions) or *absent*?

Axes (both from ontology structure, independent by construction):
  * width(c)  = |is-a descendants(c)|            — subsumption breadth.
  * depth(c)  = distinct relational triples (R,F) borne by c's descendants
                — how relationally determined the concept is; the significance
                axis, orthogonal to is-a.

Run:  .venv/bin/python src/sigml/essence_twoscale.py [cl|envo|all]
"""

from __future__ import annotations

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from obo_slice import CONFIGS, ensure_obo, parse_obo  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def build_rel_index(o):
    """entity -> set of (R, F) relational triples it bears."""
    bearer: dict[str, set] = {}
    for (R, F), xs in o.redges.items():
        for x in xs:
            bearer.setdefault(x, set()).add((R, F))
    return bearer


def width(o, c, _memo):
    if c in _memo:
        return _memo[c]
    _memo[c] = len(o.descendants(c))
    return _memo[c]


def depth_sum(o, c, bearer, _memo):
    """Total distinct (R,F) triples borne by c or any descendant. Entangled
    with width (summing over descendants inherits their count)."""
    if c in _memo:
        return _memo[c]
    triples = set()
    for d in o.descendants(c):
        triples |= bearer.get(d, set())
    _memo[c] = len(triples)
    return _memo[c]


def depth_direct(o, c, bearer, _memo):
    """Relational triples borne by the concept node ITSELF — its own
    definitional relational richness, not its subtree's. Size-independent."""
    if ("d", c) in _memo:
        return _memo[("d", c)]
    _memo[("d", c)] = len(bearer.get(c, set()))
    return _memo[("d", c)]


def depth_density(o, c, bearer, _memo, _wm):
    """Relational triples per descendant — how relationally determined the
    concept is *per unit of breadth*. Normalizes width out."""
    if ("y", c) in _memo:
        return _memo[("y", c)]
    w = width(o, c, _wm)
    _memo[("y", c)] = depth_sum(o, c, bearer, _memo) / w if w else 0.0
    return _memo[("y", c)]


def pearson(xs, ys):
    n = len(xs)
    if n < 2:
        return float("nan")
    mx, my = sum(xs) / n, sum(ys) / n
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    return sxy / math.sqrt(sxx * syy) if sxx > 0 and syy > 0 else float("nan")


def run(name):
    cfg = CONFIGS[name]
    o = parse_obo(ensure_obo(cfg), cfg["prefix"])
    bearer = build_rel_index(o)
    wm, dm = {}, {}

    # every concept that appears as a genus or differentia-filler, on both axes
    concepts = set()
    defs = []
    for t in o.genus:
        if t not in o.diff:
            continue
        G = o.genus[t]
        R, F = o.diff[t]
        if G not in o.name or F not in o.name:   # need both in-namespace
            continue
        defs.append((t, G, F))
        concepts |= {G, F}

    depth_fns = {
        "sum":     lambda c: depth_sum(o, c, bearer, dm),
        "direct":  lambda c: depth_direct(o, c, bearer, dm),
        "density": lambda c: depth_density(o, c, bearer, dm, wm),
    }

    print(f"=== {cfg['domain']} ===")
    print(f"  definitions with genus & filler in-namespace: {len(defs)}")
    print(f"  {'depth measure':10s} {'corr(width,depth)':>18s} {'genus wider':>12s}"
          f" {'diff deeper':>12s} {'inversion':>10s} {'vs chance':>10s}")
    out = {"name": name}
    ws_log = [math.log1p(width(o, c, wm)) for c in concepts]
    for key, dfn in depth_fns.items():
        r = pearson(ws_log, [math.log1p(dfn(c)) for c in concepts])
        wider = deeper = inv = n = 0
        for t, G, F in defs:
            wG, wF = width(o, G, wm), width(o, F, wm)
            dG, dF = dfn(G), dfn(F)
            if wG == wF or dG == dF:
                continue
            n += 1
            gw, fd = wG > wF, dF > dG
            wider += gw
            deeper += fd
            inv += gw and fd
        if not n:
            continue
        base = (wider / n) * (deeper / n)
        verdict = "ABOVE" if inv / n > base + 0.05 else "chance"
        print(f"  {key:10s} {r:+18.2f} {wider/n:11.0%} {deeper/n:11.0%} "
              f"{inv/n:9.0%} {verdict:>10s}")
        out[key] = {"r": r, "inversion": inv / n, "base": base, "n": n}
    return out


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    names = list(CONFIGS) if which == "all" else [which]
    res = [run(nm) for nm in names]
    if len(res) > 1:
        print("\n=== cross-domain (density depth = least width-entangled) ===")
        for x in res:
            d = x.get("density", {})
            print(f"  {x['name']:6s} corr={d.get('r', float('nan')):+.2f}  "
                  f"inversion={d.get('inversion', 0):.0%} "
                  f"(chance {d.get('base', 0):.0%})")


if __name__ == "__main__":
    main()
