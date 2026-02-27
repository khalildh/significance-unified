"""Training script for the Significance ML model.

Maps the Lean formalization to learned MNIST representations:
  - Genus: digit vs non-digit (shared)
  - Differentiae: one per digit class (10 total)
  - Raise: differentia depth > genus depth on members
  - Contrast: SimilarByContrast triplets grounding each differentia
"""

from __future__ import annotations

import argparse
import os
import time

import torch

from sigml.config import SigMLConfig, default_device
from sigml.data import make_dataloaders
from sigml.model import SignificanceModel
from sigml.losses import total_loss


def evaluate(
    model: SignificanceModel,
    loader: torch.utils.data.DataLoader,
    config: SigMLConfig,
    device: str,
) -> dict[str, float]:
    """Evaluate on a full loader. Returns metrics dict."""
    model.eval()

    genus_correct = 0
    genus_total = 0
    digit_correct = 0
    digit_total = 0
    raise_satisfied = 0
    raise_total = 0

    with torch.no_grad():
        for imgs, y_genus, y_digit in loader:
            imgs = imgs.to(device)
            y_genus = y_genus.to(device)
            y_digit = y_digit.to(device)

            logit_G, chi_G, logit_D, chi_D = model(imgs)

            # Genus accuracy
            pred_G = (logit_G > 0).float()
            genus_correct += (pred_G == y_genus).sum().item()
            genus_total += y_genus.size(0)

            # Digit accuracy (on digit images only)
            mask = y_genus > 0.5
            if mask.sum() > 0:
                pred_D = logit_D[mask].argmax(dim=1)
                digit_correct += (pred_D == y_digit[mask]).sum().item()
                digit_total += mask.sum().item()

                # Raise satisfaction
                y_d = y_digit[mask]
                chi_D_true = chi_D[mask].gather(1, y_d.unsqueeze(1)).squeeze(1)
                raise_satisfied += (chi_G[mask] < chi_D_true).sum().item()
                raise_total += mask.sum().item()

    metrics = {
        "genus_acc": genus_correct / max(genus_total, 1),
        "digit_acc": digit_correct / max(digit_total, 1),
        "raise_rate": raise_satisfied / max(raise_total, 1),
    }

    model.train()
    return metrics


def train(config: SigMLConfig, device: str = "cpu") -> str:
    """Train the full significance model. Returns path to saved checkpoint."""
    torch.manual_seed(config.seed)

    train_loader, test_loader = make_dataloaders(config)

    model = SignificanceModel(config).to(device)
    optimizer = torch.optim.AdamW(
        model.parameters(), lr=config.lr, weight_decay=config.weight_decay,
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=config.n_epochs,
    )

    os.makedirs("results", exist_ok=True)
    save_path = "results/significance_model.pt"
    best_digit_acc = 0.0

    print(f"Training on {device} for {config.n_epochs} epochs")
    print(f"{'epoch':>5}  {'total':>8}  {'genus':>8}  {'diff':>8}  "
          f"{'raise':>8}  {'contr':>8}  {'g_acc':>6}  {'d_acc':>6}  {'r_rate':>6}")
    print("-" * 82)

    for epoch in range(1, config.n_epochs + 1):
        model.train()
        epoch_losses: dict[str, float] = {}
        n_batches = 0
        t0 = time.time()

        for imgs, y_genus, y_digit in train_loader:
            imgs = imgs.to(device)
            y_genus = y_genus.to(device)
            y_digit = y_digit.to(device)

            logit_G, chi_G, logit_D, chi_D = model(imgs)

            loss, details = total_loss(
                logit_G, chi_G, logit_D, chi_D, y_genus, y_digit, config,
            )

            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

            for k, v in details.items():
                epoch_losses[k] = epoch_losses.get(k, 0.0) + v
            n_batches += 1

        scheduler.step()
        dt = time.time() - t0

        # Average losses
        for k in epoch_losses:
            epoch_losses[k] /= max(n_batches, 1)

        # Evaluate
        metrics = evaluate(model, test_loader, config, device)

        print(f"{epoch:5d}  {epoch_losses.get('total', 0):8.4f}  "
              f"{epoch_losses.get('genus', 0):8.4f}  "
              f"{epoch_losses.get('diff', 0):8.4f}  "
              f"{epoch_losses.get('raise', 0):8.4f}  "
              f"{epoch_losses.get('contrast', 0):8.4f}  "
              f"{metrics['genus_acc']:6.3f}  "
              f"{metrics['digit_acc']:6.3f}  "
              f"{metrics['raise_rate']:6.3f}")

        # Save best
        if metrics["digit_acc"] > best_digit_acc:
            best_digit_acc = metrics["digit_acc"]
            torch.save({
                "model_state_dict": model.state_dict(),
                "config": config,
                "epoch": epoch,
                "metrics": metrics,
            }, save_path)

    print(f"\nBest digit accuracy: {best_digit_acc:.4f}")
    print(f"Saved to {save_path}")
    return save_path


def main() -> None:
    parser = argparse.ArgumentParser(description="Train significance model on MNIST")
    parser.add_argument("--n-epochs", type=int, default=10)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--device", type=str, default=default_device())
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args()

    config = SigMLConfig(
        n_epochs=args.n_epochs,
        batch_size=args.batch_size,
        lr=args.lr,
        seed=args.seed,
    )
    train(config, device=args.device)


if __name__ == "__main__":
    main()
