"""
Interpretability report for unsupervised significance model.

Checks whether the discovered clusters align with the formal structure:
1. Raise satisfaction: chi_D > chi_G on every image
2. CCD witness verification: for each discovered cluster, find actual
   image triplets satisfying both gap inequalities of SimilarByContrast
3. Genus/differentia role clarity: do the depth values separate cleanly?
4. Hierarchy check: does differentia assignment predict genus assignment?

All of this is post-hoc -- the model was trained without labels.
The eval_labels are used only here to interpret what was discovered.
"""

from __future__ import annotations

import argparse
import sys
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

    # Collect all outputs
    all_chi_G, all_chi_D = [], []
    all_p_G, all_p_D = [], []
    all_z_D = []
    all_eval_labels = []

    with torch.no_grad():
        for images, eval_labels in test_loader:
            images = images.to(device)
            out = model(images)
            all_chi_G.append(out["chi_G"].cpu())
            all_chi_D.append(out["chi_D"].cpu())
            all_p_G.append(out["p_G"].cpu())
            all_p_D.append(out["p_D"].cpu())
            all_z_D.append(out["z_D"].cpu())
            all_eval_labels.append(eval_labels)

    chi_G = torch.cat(all_chi_G).numpy()
    chi_D = torch.cat(all_chi_D).numpy()
    p_G = torch.cat(all_p_G)
    p_D = torch.cat(all_p_D)
    z_D = torch.cat(all_z_D)
    eval_labels = torch.cat(all_eval_labels).numpy()

    genus_assignments = p_G.argmax(dim=-1).numpy()
    diff_assignments = p_D.argmax(dim=-1).numpy()

    print("\n" + "=" * 70)
    print("SIGNIFICANCE FORMALIZATION — UNSUPERVISED INTERPRETABILITY REPORT")
    print("=" * 70)

    # 1. Raise satisfaction
    print("\n── 1. RAISE SATISFACTION (chi_G < chi_D) ──")
    raise_rate = (chi_D > chi_G).mean()
    mean_gap = (chi_D - chi_G).mean()
    print(f"  Raise satisfied: {raise_rate * 100:.2f}% of images")
    print(f"  Mean chi_G: {chi_G.mean():.3f}")
    print(f"  Mean chi_D: {chi_D.mean():.3f}")
    print(f"  Mean gap (chi_D - chi_G): {mean_gap:.3f}")
    print(f"  Lean analogue: KonceptDef.isEssential")

    # 2. Discovered genus clusters
    print("\n── 2. DISCOVERED GENUS CLUSTERS ──")
    k_genus = model_cfg.k_genus
    for g in range(k_genus):
        mask = genus_assignments == g
        n = mask.sum()
        if n == 0:
            continue
        labels_here = eval_labels[mask]
        top = Counter(labels_here.tolist()).most_common(3)
        top_str = ", ".join(f"{label_name(int(l))}:{c}" for l, c in top)
        purity = Counter(labels_here.tolist()).most_common(1)[0][1] / n
        print(f"  Genus cluster {g}: n={n} purity={purity:.2f} "
              f"top3=[{top_str}]")
    print(f"  Lean analogue: genus.pred (which images belong to this genus?)")

    # 3. Discovered differentia clusters
    print("\n── 3. DISCOVERED DIFFERENTIA CLUSTERS ──")
    k_diff = model_cfg.k_diff
    active_diff = []
    for d in range(k_diff):
        mask = diff_assignments == d
        n = mask.sum()
        if n < 10:
            continue
        active_diff.append(d)
        labels_here = eval_labels[mask]
        top = Counter(labels_here.tolist()).most_common(3)
        top_str = ", ".join(f"{label_name(int(l))}:{c}" for l, c in top)
        purity = Counter(labels_here.tolist()).most_common(1)[0][1] / n
        genus_here = genus_assignments[mask]
        dominant_genus = Counter(genus_here.tolist()).most_common(1)[0][0]
        print(f"  Diff cluster {d:2d}: n={n:5d} purity={purity:.2f} "
              f"genus={dominant_genus} top3=[{top_str}]")
    print(f"  Active differentia clusters: {len(active_diff)}/{k_diff}")
    print(f"  Lean analogue: differentia.pred")

    # 4. CCD witnesses
    print("\n── 4. CCD WITNESSES (SimilarByContrast verification) ──")
    print(f"  {'Cluster':>10} {'Contrast':>10} "
          f"{'|a-b|':>8} {'|a-c|':>8} {'|b-c|':>8} {'Holds?':>8}")
    print("  " + "-" * 58)

    for d in active_diff[:15]:
        mask_d = (diff_assignments == d).nonzero()[0]
        if len(mask_d) < 2:
            continue

        a_idx, b_idx = mask_d[0], mask_d[1]
        chi_a = chi_D[a_idx]
        chi_b = chi_D[b_idx]

        other_mask = (diff_assignments != d).nonzero()[0]
        if len(other_mask) == 0:
            continue

        gaps_to_a = np.abs(chi_D[other_mask] - chi_a)
        c_idx = other_mask[gaps_to_a.argmax()]
        chi_c = chi_D[c_idx]

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

    # 5. Hierarchy check
    print("\n── 5. HIERARCHY CHECK (differentia -> genus) ──")
    print("  Each diff cluster should map to exactly ONE genus cluster.")
    for d in active_diff[:10]:
        mask_d = diff_assignments == d
        genus_here = genus_assignments[mask_d]
        genus_dist = Counter(genus_here.tolist())
        total = sum(genus_dist.values())
        dominant_g, dominant_n = genus_dist.most_common(1)[0]
        frac = dominant_n / total
        print(f"  Diff {d:2d} -> genus {dominant_g} ({frac * 100:.0f}% of members)")
    print(f"  Lean analogue: definiendum = genus.meet differentia")

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
