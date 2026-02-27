"""Generate interpretability report from a trained significance model.

Produces the artifacts that map back to the Lean formalization:
  1. Genus quality (digit vs non-digit accuracy)
  2. Meet-like behavior (definiendum ~ genus AND differentia)
  3. Raise validity (chi_G < chi_D[true_digit] rate)
  4. CCDWitness triplets (visual contrast examples)
  5. ccd_contrast check (contrast lacks differentia)
"""

from __future__ import annotations

import argparse
import os

import torch
import torch.nn.functional as F

from sigml.config import SigMLConfig, default_device
from sigml.data import DigitNonDigitDataset
from sigml.model import SignificanceModel


def load_model(
    path: str, device: str,
) -> tuple[SignificanceModel, SigMLConfig]:
    """Load trained model from checkpoint."""
    checkpoint = torch.load(path, map_location=device, weights_only=False)
    config = checkpoint["config"]
    model = SignificanceModel(config).to(device)
    model.load_state_dict(checkpoint["model_state_dict"])
    model.eval()
    return model, config


def find_ccd_witnesses(
    model: SignificanceModel,
    dataset: DigitNonDigitDataset,
    device: str,
    n_per_digit: int = 3,
) -> dict[int, list[dict]]:
    """Find CCDWitness-style triplets for each digit.

    For digit i, find (anchor, positive, contrast) where:
      - anchor and positive are digit i
      - contrast is a different digit (same genus, different differentia)
      - SimilarByContrast gap inequalities are maximally satisfied

    Returns dict mapping digit -> list of witness dicts.
    """
    # Collect digit images by class, along with their chi_D scores
    digit_images: dict[int, list[tuple[torch.Tensor, float]]] = {d: [] for d in range(10)}

    batch_size = 512
    n_items = len(dataset.mnist)  # only MNIST portion

    with torch.no_grad():
        for start in range(0, n_items, batch_size):
            end = min(start + batch_size, n_items)
            batch_imgs = []
            batch_labels = []
            for idx in range(start, end):
                img, _, label = dataset[idx]
                batch_imgs.append(img)
                batch_labels.append(label)

            imgs = torch.stack(batch_imgs).to(device)
            labels = torch.tensor(batch_labels, device=device)

            _, _, _, chi_D = model(imgs)

            for j in range(imgs.size(0)):
                d = labels[j].item()
                chi_val = chi_D[j, d].item()
                digit_images[d].append((batch_imgs[j], chi_val))

    witnesses: dict[int, list[dict]] = {}

    for digit in range(10):
        members = digit_images[digit]
        if len(members) < 2:
            continue

        # Sort by chi_D value for this digit
        members.sort(key=lambda x: x[1])

        # Pick anchor (median) and positive (close neighbor)
        mid = len(members) // 2
        anchor_img, anchor_chi = members[mid]
        pos_img, pos_chi = members[mid + 1] if mid + 1 < len(members) else members[mid - 1]

        d_ab = abs(anchor_chi - pos_chi)

        # Find best contrast from another digit
        best_witnesses = []
        for other_digit in range(10):
            if other_digit == digit:
                continue
            for con_img, con_chi in digit_images[other_digit][:20]:
                d_ac = abs(anchor_chi - con_chi)
                d_bc = abs(pos_chi - con_chi)
                # SimilarByContrast margin satisfaction
                satisfaction = (d_ac - d_ab) + (d_bc - d_ab)
                best_witnesses.append({
                    "anchor_img": anchor_img,
                    "pos_img": pos_img,
                    "con_img": con_img,
                    "anchor_chi": anchor_chi,
                    "pos_chi": pos_chi,
                    "con_chi": con_chi,
                    "d_ab": d_ab,
                    "d_ac": d_ac,
                    "d_bc": d_bc,
                    "satisfaction": satisfaction,
                    "contrast_digit": other_digit,
                })

        # Keep top witnesses
        best_witnesses.sort(key=lambda w: w["satisfaction"], reverse=True)
        witnesses[digit] = best_witnesses[:n_per_digit]

    return witnesses


def generate_report(model_path: str, device: str) -> None:
    """Print a full interpretability report."""
    model, config = load_model(model_path, device)
    dataset = DigitNonDigitDataset(train=False)

    print("=" * 60)
    print("SIGNIFICANCE MODEL — INTERPRETABILITY REPORT")
    print("=" * 60)

    # 1. Genus quality
    print("\n1. GENUS (digit vs non-digit)")
    print("-" * 40)
    genus_correct = 0
    genus_total = 0
    digit_correct = 0
    digit_total = 0
    raise_satisfied = 0
    raise_total = 0
    meet_correct = 0

    batch_size = 512
    all_chi_G_digits: list[float] = []
    all_chi_D_true: list[float] = []

    with torch.no_grad():
        for start in range(0, len(dataset), batch_size):
            end = min(start + batch_size, len(dataset))
            batch_imgs, batch_genus, batch_digit = [], [], []
            for idx in range(start, end):
                img, g, d = dataset[idx]
                batch_imgs.append(img)
                batch_genus.append(g)
                batch_digit.append(d)

            imgs = torch.stack(batch_imgs).to(device)
            y_genus = torch.tensor(batch_genus, device=device)
            y_digit = torch.tensor(batch_digit, device=device)

            logit_G, chi_G, logit_D, chi_D = model(imgs)

            # Genus accuracy
            pred_G = (logit_G > 0).float()
            genus_correct += (pred_G == y_genus).sum().item()
            genus_total += y_genus.size(0)

            mask = y_genus > 0.5
            if mask.sum() > 0:
                # Digit accuracy
                pred_D = logit_D[mask].argmax(dim=1)
                digit_correct += (pred_D == y_digit[mask]).sum().item()
                digit_total += mask.sum().item()

                # Meet-like: argmax(p_G * sigmoid(logit_D))
                p_G = torch.sigmoid(logit_G[mask]).unsqueeze(1)  # [N, 1]
                p_D = torch.sigmoid(logit_D[mask])               # [N, 10]
                p_meet = p_G * p_D
                pred_meet = p_meet.argmax(dim=1)
                meet_correct += (pred_meet == y_digit[mask]).sum().item()

                # Raise
                y_d = y_digit[mask]
                chi_D_true = chi_D[mask].gather(1, y_d.unsqueeze(1)).squeeze(1)
                raise_satisfied += (chi_G[mask] < chi_D_true).sum().item()
                raise_total += mask.sum().item()

                all_chi_G_digits.extend(chi_G[mask].cpu().tolist())
                all_chi_D_true.extend(chi_D_true.cpu().tolist())

    print(f"  Genus accuracy:          {genus_correct / genus_total:.4f}")

    # 2. Differentia quality
    print(f"\n2. DIFFERENTIAE (10 digit classes)")
    print("-" * 40)
    print(f"  Digit accuracy (argmax): {digit_correct / max(digit_total, 1):.4f}")
    print(f"  Meet accuracy (pG*pDi):  {meet_correct / max(digit_total, 1):.4f}")

    # 3. Raise validity
    print(f"\n3. RAISE (isEssential: chi_G < chi_D[true])")
    print("-" * 40)
    print(f"  Raise satisfaction rate: {raise_satisfied / max(raise_total, 1):.4f}")
    if all_chi_G_digits:
        avg_G = sum(all_chi_G_digits) / len(all_chi_G_digits)
        avg_D = sum(all_chi_D_true) / len(all_chi_D_true)
        print(f"  Mean chi_G on digits:    {avg_G:.4f}")
        print(f"  Mean chi_D[true]:        {avg_D:.4f}")
        print(f"  Mean gap (D - G):        {avg_D - avg_G:.4f}")

    # 4. CCDWitness triplets
    print(f"\n4. CCD WITNESSES (SimilarByContrast triplets)")
    print("-" * 40)
    witnesses = find_ccd_witnesses(model, dataset, device, n_per_digit=2)
    for digit in range(10):
        if digit not in witnesses or not witnesses[digit]:
            continue
        print(f"\n  Digit {digit}:")
        for i, w in enumerate(witnesses[digit]):
            print(f"    Witness {i+1}: contrast=digit {w['contrast_digit']}")
            print(f"      chi(a)={w['anchor_chi']:.3f}  chi(b)={w['pos_chi']:.3f}  "
                  f"chi(c)={w['con_chi']:.3f}")
            print(f"      |a-b|={w['d_ab']:.3f}  |a-c|={w['d_ac']:.3f}  "
                  f"|b-c|={w['d_bc']:.3f}")
            holds = w['d_ab'] < w['d_ac'] and w['d_ab'] < w['d_bc']
            print(f"      SimilarByContrast holds: {holds}")

    # 5. ccd_contrast check
    print(f"\n5. CCD_CONTRAST (contrast lacks differentia)")
    print("-" * 40)
    for digit in range(10):
        if digit not in witnesses or not witnesses[digit]:
            continue
        w = witnesses[digit][0]
        con_digit = w['contrast_digit']
        print(f"  Digit {digit}: contrast is digit {con_digit} "
              f"(not differentia {digit}) ✓")

    print("\n" + "=" * 60)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate interpretability report")
    parser.add_argument("--model", type=str, default="results/significance_model.pt")
    parser.add_argument("--device", type=str, default=default_device())
    args = parser.parse_args()

    generate_report(args.model, args.device)


if __name__ == "__main__":
    main()
