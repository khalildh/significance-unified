"""Does the representation actually learn the hierarchy? Measure, don't assume.

Every audit in this project consumes positions from an order embedding trained
on the is-a graph — and until now nobody checked the embedding is any good. If
it never converged, the audit was faithfully checking noise against the spec.
This is the ML-side analogue of the Python≡Lean validation: quantify how
faithfully the learned representation encodes the taxonomy it was trained on.

An order embedding (Vendrov et al.) should place a hyponym so that it dominates
its hypernym on every coordinate — `emb(child) ≥ emb(parent)`, energy
`‖max(0, parent − child)‖² = 0`. Three metrics, held-out where it matters:

  * order-property rate — fraction of is-a edges with child ≥ parent everywhere
    (the defining constraint; 1.0 = perfectly satisfied).
  * reconstruction AUC   — can edge energy separate true is-a edges from random
    non-edges? (0.5 = chance, 1.0 = perfect). Computed on a HELD-OUT edge split
    so it measures generalization, not memorization.
  * collapse check       — per-dimension spread; a degenerate embedding that
    pushes everything to one point would ace nothing and must be caught.

    sigml repr [cl|envo|all]
"""

from __future__ import annotations

import os
import sys

import numpy as np
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from obo_slice import CONFIGS, ensure_obo, parse_obo, train_positions  # noqa: E402

SEED = 3


def train_better(nodes, edges, seed, dim=32, steps=6000):
    """A properly-sized order embedding: higher dimension, more steps, batched
    negatives. Same Vendrov energy as the audit's tiny trainer — the question
    is whether the audits' weak embeddings were under-training or a real ceiling."""
    torch.manual_seed(seed)
    idx = {n: i for i, n in enumerate(sorted(nodes))}
    emb = torch.nn.Parameter(torch.rand(len(nodes), dim) * 0.3 + 0.1)
    pairs = torch.tensor([[idx[a], idx[b]] for a, b in edges])
    opt = torch.optim.Adam([emb], lr=0.1)
    g = torch.Generator().manual_seed(seed)
    for _ in range(steps):
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


def isa_edges(o, cap_nodes=1200):
    """(child, parent) is-a edges over a bounded node set."""
    nodes = list(o.name)[:cap_nodes]
    ns = set(nodes)
    edges = [(c, p) for c in nodes for p in o.is_a.get(c, []) if p in ns]
    return ns, edges


def closure_edges(o, ns):
    """(descendant, ancestor) pairs — the transitive closure of is-a, which is
    the standard training signal for order embeddings (Vendrov et al.)."""
    pairs = set()
    for c in ns:
        stack, seen = list(o.is_a.get(c, [])), set()
        while stack:
            p = stack.pop()
            if p in seen or p not in ns:
                continue
            seen.add(p)
            pairs.add((c, p))
            stack.extend(o.is_a.get(p, []))
    return list(pairs)


def energy(emb, a, b):
    """Order-embedding energy: how much `a` (child) fails to dominate `b`."""
    return float(np.square(np.maximum(0.0, emb[b] - emb[a])).sum())


def auc(pos, neg):
    """Probability a random true edge has lower energy than a random non-edge."""
    pos, neg = np.array(pos), np.array(neg)
    wins = sum((pos[:, None] < neg[None, :]).sum(1))
    ties = sum((pos[:, None] == neg[None, :]).sum(1))
    return (wins + 0.5 * ties) / (len(pos) * len(neg))


def run(name):
    cfg = CONFIGS[name]
    o = parse_obo(ensure_obo(cfg), cfg["prefix"])
    nodes, edges = isa_edges(o)
    rng = np.random.default_rng(SEED)
    rng.shuffle(edges)
    split = int(0.85 * len(edges))
    train_e, test_e = edges[:split], edges[split:]

    nl = list(nodes)
    edgeset = set(edges)
    negs = []
    while len(negs) < len(test_e):
        a, b = rng.choice(nl), rng.choice(nl)
        if a != b and (a, b) not in edgeset:
            negs.append((a, b))

    def measure(emb):
        order_ok = np.mean([all(emb[c] >= emb[p]) for c, p in test_e])
        pos_e = [energy(emb, c, p) for c, p in test_e]
        neg_e = [energy(emb, a, b) for a, b in negs]
        mat = np.array([emb[n] for n in nodes])
        return order_ok, auc(pos_e, neg_e), float(mat.std(axis=0).mean())

    print(f"=== {cfg['domain']} ===")
    print(f"  nodes {len(nodes)}  is-a edges {len(edges)} "
          f"(train {len(train_e)} / test {len(test_e)})")
    print(f"  {'configuration':28s} {'order':>7s} {'AUC':>6s} {'spread':>7s}")
    o_def = measure(train_positions(nodes, set(train_e), SEED))
    print(f"  {'audit default (6-D, 1.2k)':28s} {o_def[0]:7.2f} {o_def[1]:6.2f} "
          f"{o_def[2]:7.2f}")
    o_big = measure(train_better(nodes, set(train_e), SEED))
    print(f"  {'proper (32-D, 6k steps)':28s} {o_big[0]:7.2f} {o_big[1]:6.2f} "
          f"{o_big[2]:7.2f}")
    # standard setup: train AND evaluate on the transitive closure
    clo = closure_edges(o, nodes)
    rng.shuffle(clo)
    csplit = int(0.85 * len(clo))
    ctrain, ctest = clo[:csplit], clo[csplit:]
    cneg = []
    cset = set(clo)
    while len(cneg) < len(ctest):
        a, b = rng.choice(nl), rng.choice(nl)
        if a != b and (a, b) not in cset:
            cneg.append((a, b))
    emb_c = train_better(nodes, set(ctrain), SEED)
    c_order = np.mean([all(emb_c[c] >= emb_c[p]) for c, p in ctest])
    c_auc = auc([energy(emb_c, c, p) for c, p in ctest],
                [energy(emb_c, a, b) for a, b in cneg])
    c_spread = float(np.array([emb_c[n] for n in nodes]).std(axis=0).mean())
    print(f"  {'+ transitive closure (32-D)':28s} {c_order:7.2f} {c_auc:6.2f} "
          f"{c_spread:7.2f}   ({len(clo)} closure edges)")
    return {"name": name, "default": o_def, "better": o_big,
            "closure": (c_order, c_auc, c_spread)}


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    names = list(CONFIGS) if which == "all" else [which]
    res = [run(nm) for nm in names]
    print("\n=== summary (reconstruction AUC across setups) ===")
    for x in res:
        d, b, c = x["default"], x["better"], x["closure"]
        best = max(d[1], b[1], c[1])
        verdict = ("faithful with proper setup" if best > 0.85
                   else "partial even properly set up" if best > 0.7
                   else "weak — representation does not encode the taxonomy")
        print(f"  {x['name']:6s} default {d[1]:.2f} | +scale {b[1]:.2f} | "
              f"+closure {c[1]:.2f}  → {verdict}")


if __name__ == "__main__":
    main()
