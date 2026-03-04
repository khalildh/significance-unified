"""
Interpretability report for unsupervised N-level significance model.

Checks whether the discovered hierarchy aligns with the formal structure:
1. Raise satisfaction: chi increases at each level
2. Discovered clusters: per alive level with purity, size, top-3 labels
3. CCD witness verification: at the finest alive level
4. Hierarchy check: does each finer level predict its coarser parent?
5. CCD₃ coverage: per alive level
6. Hierarchy summary: compact view of alive/dead levels and effective depth

All of this is post-hoc -- the model was trained without labels.
The eval_labels are used only here to interpret what was discovered.
"""

from __future__ import annotations

import argparse
from collections import Counter

import torch
import numpy as np

from sigml.unsup_data import DataConfig, make_loaders
from sigml.unsup_model import ModelConfig, SigMLUnsupervised


FASHION_NAMES = [
    "T-shirt", "Trouser", "Pullover", "Dress", "Coat",
    "Sandal", "Shirt", "Sneaker", "Bag", "Boot"
]
DIGIT_NAMES = [str(i) for i in range(10)]


def label_name(eval_label: int) -> str:
    if eval_label < 10:
        return f"digit-{DIGIT_NAMES[eval_label]}"
    return f"fashion-{FASHION_NAMES[eval_label - 10]}"


def generate_report(model_path: str | None = None) -> None:
    if torch.cuda.is_available():
        device = "cuda"
    elif torch.backends.mps.is_available():
        device = "mps"
    else:
        device = "cpu"

    if model_path:
        checkpoint = torch.load(model_path, map_location=device, weights_only=False)
        model_cfg = checkpoint["model_config"]
        model = SigMLUnsupervised(model_cfg).to(device)
        model.load_state_dict(checkpoint["model_state_dict"])
        print(f"Loaded model from {model_path}")
    else:
        model_cfg = ModelConfig()
        model = SigMLUnsupervised(model_cfg).to(device)
        print("WARNING: No model path provided, using random weights")

    model.eval()

    _, test_loader = make_loaders(DataConfig())

    # Collect all outputs per level
    n_levels = len(model.levels)
    all_chi = [[] for _ in range(n_levels)]
    all_p = [[] for _ in range(n_levels)]
    all_z = [[] for _ in range(n_levels)]
    all_eval_labels = []

    with torch.no_grad():
        for images, eval_labels in test_loader:
            images = images.to(device)
            out = model(images)
            for i, lvl in enumerate(out["levels"]):
                all_chi[i].append(lvl["chi"].cpu())
                all_p[i].append(lvl["p"].cpu())
                all_z[i].append(lvl["z"].cpu())
            all_eval_labels.append(eval_labels)

    # Per-level tensors
    level_data = []
    for i in range(n_levels):
        chi = torch.cat(all_chi[i]).numpy()
        p = torch.cat(all_p[i])
        z = torch.cat(all_z[i])
        assignments = p.argmax(dim=-1).numpy()
        level_data.append({
            "chi": chi,
            "p": p,
            "z": z,
            "assignments": assignments,
        })

    eval_labels = torch.cat(all_eval_labels).numpy()
    alive_indices = [i for i in range(n_levels) if model.levels[i].is_alive]
    ks = model_cfg.k_per_level()

    print("\n" + "=" * 70)
    print("SIGNIFICANCE FORMALIZATION — UNSUPERVISED INTERPRETABILITY REPORT")
    print("=" * 70)

    # ── 1. RAISE SATISFACTION ──
    print("\n── 1. RAISE SATISFACTION (chi_i < chi_{i+1}) ──")
    for i in range(n_levels - 1):
        chi_lo = level_data[i]["chi"]
        chi_hi = level_data[i + 1]["chi"]
        rate = (chi_hi > chi_lo).mean()
        gap = (chi_hi - chi_lo).mean()
        print(f"  L{i}→L{i+1}: {rate * 100:.1f}% satisfied  "
              f"(mean gap: {gap:.3f})")

    # Overall chain across alive levels
    if len(alive_indices) >= 2:
        chain_ok = np.ones(len(eval_labels), dtype=bool)
        for j in range(len(alive_indices) - 1):
            lo = alive_indices[j]
            hi = alive_indices[j + 1]
            chain_ok &= level_data[hi]["chi"] > level_data[lo]["chi"]
        print(f"  Overall chain (alive levels): {chain_ok.mean() * 100:.1f}%")

    # Depth profile
    print("  Depth profile (mean chi per level):")
    for i in range(n_levels):
        status = "alive" if i in alive_indices else "DEAD"
        print(f"    L{i}: mean_chi={level_data[i]['chi'].mean():.3f}  [{status}]")
    print(f"  Lean analogue: SignificanceRaise.compose (transitive depth ordering)")

    # ── 2. DISCOVERED CLUSTERS ──
    print("\n── 2. DISCOVERED CLUSTERS (per alive level) ──")
    for i in alive_indices:
        assignments = level_data[i]["assignments"]
        k = ks[i]
        eff_k = model.levels[i].effective_k
        print(f"\n  Level {i} ({eff_k} active / {k} total):")

        for c in range(k):
            mask = assignments == c
            n = mask.sum()
            if n < 10:
                continue
            labels_here = eval_labels[mask]
            top = Counter(labels_here.tolist()).most_common(3)
            top_str = ", ".join(f"{label_name(int(l))}:{cnt}" for l, cnt in top)
            purity = Counter(labels_here.tolist()).most_common(1)[0][1] / n
            print(f"    Cluster {c:2d}: n={n:5d} purity={purity:.2f} "
                  f"top3=[{top_str}]")

    # ── 3. CCD WITNESSES ──
    print("\n── 3. CCD WITNESSES (SimilarByContrast at finest alive level) ──")
    if alive_indices:
        finest = alive_indices[-1]
        assignments = level_data[finest]["assignments"]
        chi = level_data[finest]["chi"]
        k = ks[finest]

        # Find active clusters
        active = [c for c in range(k) if (assignments == c).sum() >= 10]

        print(f"  Level {finest} — {len(active)} active clusters")
        print(f"  {'Cluster':>10} {'Contrast':>10} "
              f"{'|a-b|':>8} {'|a-c|':>8} {'|b-c|':>8} {'Holds?':>8}")
        print("  " + "-" * 58)

        for d in active[:15]:
            mask_d = np.where(assignments == d)[0]
            if len(mask_d) < 2:
                continue

            a_idx, b_idx = mask_d[0], mask_d[1]
            chi_a = chi[a_idx]
            chi_b = chi[b_idx]

            other_mask = np.where(assignments != d)[0]
            if len(other_mask) == 0:
                continue

            gaps_to_a = np.abs(chi[other_mask] - chi_a)
            c_idx = other_mask[gaps_to_a.argmax()]
            chi_c = chi[c_idx]

            gap_ab = abs(chi_a - chi_b)
            gap_ac = abs(chi_a - chi_c)
            gap_bc = abs(chi_b - chi_c)
            holds = gap_ab < gap_ac and gap_ab < gap_bc

            contrast_label = label_name(int(eval_labels[c_idx]))
            cluster_label = label_name(int(eval_labels[a_idx]))

            print(f"  {cluster_label:>10} {contrast_label:>10} "
                  f"{gap_ab:>8.3f} {gap_ac:>8.3f} {gap_bc:>8.3f} "
                  f"{'Y' if holds else 'X':>8}")

        print(f"  Lean analogue: CCDWitness3")

    # ── 4. HIERARCHY CHECK ──
    print("\n── 4. HIERARCHY CHECK (finer level → coarser level) ──")
    print("  Each cluster at level i+1 should map to one cluster at level i.")
    for j in range(len(alive_indices) - 1):
        lo = alive_indices[j]
        hi = alive_indices[j + 1]
        assignments_hi = level_data[hi]["assignments"]
        assignments_lo = level_data[lo]["assignments"]
        k_hi = ks[hi]

        active_hi = [c for c in range(k_hi) if (assignments_hi == c).sum() >= 10]
        print(f"\n  L{hi} → L{lo} ({len(active_hi)} active clusters at L{hi}):")

        for d in active_hi[:10]:
            mask_d = assignments_hi == d
            lo_here = assignments_lo[mask_d]
            lo_dist = Counter(lo_here.tolist())
            total = sum(lo_dist.values())
            dominant_c, dominant_n = lo_dist.most_common(1)[0]
            frac = dominant_n / total
            print(f"    L{hi} cluster {d:2d} → L{lo} cluster {dominant_c} "
                  f"({frac * 100:.0f}% of members)")

    print(f"  Lean analogue: definiendum = genus.meet differentia (composed via chain)")

    # ── 5. CCD₃ COVERAGE ──
    print("\n── 5. CCD₃ COVERAGE (SimilarByContrast over embeddings) ──")
    print("  For each active cluster, sample triplets (a, b from cluster,")
    print("  c from outside) and check both gap inequalities hold.")
    rng = np.random.default_rng(42)
    max_triplets = 100

    def ccd3_coverage(assignments, embeddings, cluster_ids):
        per_cluster = {}
        for c in cluster_ids:
            in_mask = np.where(assignments == c)[0]
            out_mask = np.where(assignments != c)[0]
            if len(in_mask) < 2 or len(out_mask) == 0:
                continue
            n_pairs = min(max_triplets, len(in_mask) * (len(in_mask) - 1) // 2)
            satisfied = 0
            for _ in range(n_pairs):
                idx_ab = rng.choice(len(in_mask), size=2, replace=False)
                a, b = in_mask[idx_ab[0]], in_mask[idx_ab[1]]
                c_idx = out_mask[rng.integers(len(out_mask))]
                z_a = embeddings[a]
                z_b = embeddings[b]
                z_c = embeddings[c_idx]
                gap_ab = torch.norm(z_a - z_b).item()
                gap_ac = torch.norm(z_a - z_c).item()
                gap_bc = torch.norm(z_b - z_c).item()
                if gap_ab < gap_ac and gap_ab < gap_bc:
                    satisfied += 1
            per_cluster[c] = satisfied / n_pairs
        return per_cluster

    for i in alive_indices:
        assignments = level_data[i]["assignments"]
        z = level_data[i]["z"]
        k = ks[i]
        active = [c for c in range(k) if (assignments == c).sum() >= 10]
        ccd3 = ccd3_coverage(assignments, z, active)

        print(f"\n  Level {i} ({len(ccd3)} active clusters):")
        for c, cov in sorted(ccd3.items()):
            n = (assignments == c).sum()
            print(f"    Cluster {c:2d}: coverage={cov:.3f}  (n={n})")
        if ccd3:
            mean_cov = np.mean(list(ccd3.values()))
            print(f"    Level {i} mean CCD₃: {mean_cov:.3f}")

    print(f"  Lean analogue: SimilarByContrast (gap inequalities on embedding space)")

    # ── 6. HIERARCHY SUMMARY ──
    print("\n── 6. HIERARCHY SUMMARY ──")
    print(f"  Overcomplete levels: {n_levels}")
    print(f"  Effective depth: {len(alive_indices)}")
    print(f"  Alive levels: {alive_indices}")
    print()
    for i in range(n_levels):
        eff_k = model.levels[i].effective_k
        status = "ALIVE" if i in alive_indices else "DEAD"
        mean_chi = level_data[i]["chi"].mean()

        if i in alive_indices:
            assignments = level_data[i]["assignments"]
            purity_vals = []
            for c in range(ks[i]):
                mask = assignments == c
                n = mask.sum()
                if n < 10:
                    continue
                labels_here = eval_labels[mask]
                majority = Counter(labels_here.tolist()).most_common(1)[0][1]
                purity_vals.append(majority / n)
            mean_pur = np.mean(purity_vals) if purity_vals else 0.0
            print(f"  L{i}: {status:5s}  k={eff_k:3d}/{ks[i]:<3d}  "
                  f"mean_chi={mean_chi:6.3f}  mean_purity={mean_pur:.3f}")
        else:
            print(f"  L{i}: {status:5s}  k={eff_k:3d}/{ks[i]:<3d}  "
                  f"mean_chi={mean_chi:6.3f}")

    print(f"\n  Lean analogue: KonceptDef.chain with chain_depth_bound")

    print("\n" + "=" * 70)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate unsupervised interpretability report"
    )
    parser.add_argument("--model", type=str, default="results/unsup_model.pt")
    args = parser.parse_args()
    generate_report(args.model)


if __name__ == "__main__":
    main()
