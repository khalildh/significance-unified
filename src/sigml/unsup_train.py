"""
Training loop for unsupervised significance learning.

No labels are used during training. Evaluation uses eval_labels
to measure cluster quality post-hoc via cluster purity.
"""

from __future__ import annotations

import argparse
import os
import time

import torch
import torch.optim as optim
from collections import Counter
from dataclasses import dataclass, field

from sigml.unsup_data import DataConfig, make_loaders
from sigml.unsup_model import ModelConfig, SigMLUnsupervised
from sigml.unsup_losses import LossConfig, total_loss


@dataclass
class TrainConfig:
    n_epochs: int = 30
    lr: float = 3e-4
    device: str = ""
    data: DataConfig = field(default_factory=DataConfig)
    model: ModelConfig = field(default_factory=ModelConfig)
    loss: LossConfig = field(default_factory=LossConfig)

    def __post_init__(self) -> None:
        if not self.device:
            if torch.cuda.is_available():
                self.device = "cuda"
            elif torch.backends.mps.is_available():
                self.device = "mps"
            else:
                self.device = "cpu"


def cluster_purity(assignments: torch.Tensor, eval_labels: torch.Tensor) -> float:
    """
    Cluster purity: for each discovered cluster, what fraction of its members
    share the most common eval_label?

    Computed post-hoc — never fed back to the model.
    """
    n = assignments.shape[0]
    k = assignments.max().item() + 1
    correct = 0
    for c in range(int(k)):
        mask = assignments == c
        if mask.sum() == 0:
            continue
        labels_in_cluster = eval_labels[mask]
        majority = labels_in_cluster.bincount().max().item()
        correct += majority
    return correct / n


def raise_satisfaction_rate(chi_G: torch.Tensor, chi_D: torch.Tensor) -> float:
    """Fraction of images where chi_D > chi_G (Raise satisfied)."""
    return (chi_D > chi_G).float().mean().item()


def evaluate(model: SigMLUnsupervised, loader, device: str) -> dict[str, float]:
    model.eval()

    all_chi_G, all_chi_D = [], []
    all_p_G, all_p_D = [], []
    all_eval_labels = []

    with torch.no_grad():
        for images, eval_labels in loader:
            images = images.to(device)
            out = model(images)
            all_chi_G.append(out["chi_G"].cpu())
            all_chi_D.append(out["chi_D"].cpu())
            all_p_G.append(out["p_G"].cpu())
            all_p_D.append(out["p_D"].cpu())
            all_eval_labels.append(eval_labels)

    chi_G = torch.cat(all_chi_G)
    chi_D = torch.cat(all_chi_D)
    p_G = torch.cat(all_p_G)
    p_D = torch.cat(all_p_D)
    eval_labels = torch.cat(all_eval_labels)

    genus_assignments = p_G.argmax(dim=-1)
    diff_assignments = p_D.argmax(dim=-1)

    raise_rate = raise_satisfaction_rate(chi_G, chi_D)
    genus_purity = cluster_purity(genus_assignments, eval_labels)
    diff_purity = cluster_purity(diff_assignments, eval_labels)

    genus_used = (p_G.mean(0) > 0.01).sum().item()
    diff_used = (p_D.mean(0) > 0.01).sum().item()

    mean_chi_G = chi_G.mean().item()
    mean_chi_D = chi_D.mean().item()
    mean_gap = (chi_D - chi_G).mean().item()

    model.train()
    return {
        "raise_rate": raise_rate,
        "genus_purity": genus_purity,
        "diff_purity": diff_purity,
        "genus_clusters_used": genus_used,
        "diff_clusters_used": diff_used,
        "mean_chi_G": mean_chi_G,
        "mean_chi_D": mean_chi_D,
        "mean_gap": mean_gap,
    }


def train(cfg: TrainConfig) -> str:
    device = cfg.device
    print(f"Device: {device}")

    train_loader, test_loader = make_loaders(cfg.data)

    model = SigMLUnsupervised(cfg.model).to(device)
    optimizer = optim.AdamW(model.parameters(), lr=cfg.lr)
    scheduler = optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=cfg.n_epochs
    )

    os.makedirs("results", exist_ok=True)
    save_path = "results/unsup_model.pt"

    print(f"\nTraining for {cfg.n_epochs} epochs")
    print(f"Genus clusters to discover: {cfg.model.k_genus}")
    print(f"Differentia clusters to discover: {cfg.model.k_diff}")
    print("No labels used during training.\n")

    header = (
        f"{'ep':>3} | {'total':>6} {'gc':>6} {'dc':>6} "
        f"{'raise':>6} {'hier':>6} {'unif':>6} | "
        f"{'r_rate':>6} {'g_pur':>6} {'d_pur':>6} | "
        f"{'G_cl':>4} {'D_cl':>4} | "
        f"{'chi_G':>6} {'chi_D':>6} {'gap':>6}"
    )
    print(header)
    print("-" * len(header))

    best_diff_purity = 0.0

    warmup_epochs = max(1, cfg.n_epochs // 5)

    for epoch in range(1, cfg.n_epochs + 1):
        model.train()
        epoch_losses: dict[str, float] = {}
        n_batches = 0
        t0 = time.time()

        # Warmup: ramp contrast weights over first few epochs
        warmup_factor = min(1.0, epoch / warmup_epochs)
        loss_cfg = LossConfig(
            w_genus=cfg.loss.w_genus * warmup_factor,
            w_diff=cfg.loss.w_diff * warmup_factor,
            w_raise=cfg.loss.w_raise,
            w_hier=cfg.loss.w_hier,
            w_unif=cfg.loss.w_unif,
            contrast_margin=cfg.loss.contrast_margin,
            contrast_threshold=cfg.loss.contrast_threshold,
            max_triplets=cfg.loss.max_triplets,
            raise_margin=cfg.loss.raise_margin,
        )

        for images, _eval_labels in train_loader:
            images = images.to(device)

            optimizer.zero_grad()
            out = model(images)
            loss, breakdown = total_loss(out, loss_cfg)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()

            for k, v in breakdown.items():
                epoch_losses[k] = epoch_losses.get(k, 0.0) + v
            n_batches += 1

        scheduler.step()

        for k in epoch_losses:
            epoch_losses[k] /= max(n_batches, 1)

        metrics = evaluate(model, test_loader, device)

        print(
            f"{epoch:3d} | "
            f"{epoch_losses.get('total', 0):6.3f} "
            f"{epoch_losses.get('genus_contrast', 0):6.3f} "
            f"{epoch_losses.get('diff_contrast', 0):6.3f} "
            f"{epoch_losses.get('raise', 0):6.3f} "
            f"{epoch_losses.get('hierarchy', 0):6.3f} "
            f"{epoch_losses.get('uniform', 0):6.3f} | "
            f"{metrics['raise_rate']:6.3f} "
            f"{metrics['genus_purity']:6.3f} "
            f"{metrics['diff_purity']:6.3f} | "
            f"{metrics['genus_clusters_used']:4.0f} "
            f"{metrics['diff_clusters_used']:4.0f} | "
            f"{metrics['mean_chi_G']:6.2f} "
            f"{metrics['mean_chi_D']:6.2f} "
            f"{metrics['mean_gap']:6.2f}"
        )

        if metrics["diff_purity"] > best_diff_purity:
            best_diff_purity = metrics["diff_purity"]
            torch.save({
                "model_state_dict": model.state_dict(),
                "model_config": cfg.model,
                "loss_config": cfg.loss,
                "epoch": epoch,
                "metrics": metrics,
            }, save_path)

    print(f"\nBest differentia purity: {best_diff_purity:.4f}")
    print(f"Saved to {save_path}")
    return save_path


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Train unsupervised significance model"
    )
    parser.add_argument("--n-epochs", type=int, default=30)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--k-genus", type=int, default=4)
    parser.add_argument("--k-diff", type=int, default=20)
    parser.add_argument("--device", type=str, default="")
    args = parser.parse_args()

    cfg = TrainConfig(
        n_epochs=args.n_epochs,
        lr=args.lr,
        device=args.device,
        data=DataConfig(batch_size=args.batch_size),
        model=ModelConfig(k_genus=args.k_genus, k_diff=args.k_diff),
    )
    train(cfg)


if __name__ == "__main__":
    main()
