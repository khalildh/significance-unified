"""
Training loop for unsupervised significance learning with N-level hierarchy.

No labels are used during training. Evaluation uses eval_labels
to measure cluster quality post-hoc via cluster purity.

Both width (prototypes per level) and depth (number of alive levels)
are discovered via overcomplete initialization + CCD₃ witnessability pruning.
"""

from __future__ import annotations

import argparse
import os
import time
from dataclasses import dataclass, field, replace

import torch
import torch.optim as optim

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


def raise_satisfaction_rate(chi_lo: torch.Tensor, chi_hi: torch.Tensor) -> float:
    """Fraction of images where chi_hi > chi_lo (Raise satisfied)."""
    return (chi_hi > chi_lo).float().mean().item()


def ccd_witnessability(
    embeddings: torch.Tensor,
    assignments: torch.Tensor,
    k: int,
    n_triplets: int = 50,
    min_cluster_size: int = 2,
) -> torch.Tensor:
    """Per-cluster CCD₃ witnessability: fraction of sampled triplets where
    both SimilarByContrast gap inequalities hold.

    A cluster that can't produce witnesses is an ungrounded abstraction.
    For random partitions, expected score is ~1/3 (one of three gaps is
    smallest with equal probability). Well-separated clusters score >0.8.
    """
    scores = torch.zeros(k)
    for c in range(k):
        in_idx = (assignments == c).nonzero(as_tuple=True)[0]
        out_idx = (assignments != c).nonzero(as_tuple=True)[0]
        if len(in_idx) < min_cluster_size or len(out_idx) == 0:
            scores[c] = 0.0
            continue
        n = min(n_triplets, len(in_idx) * (len(in_idx) - 1) // 2)
        # Sample pairs from within cluster
        pair_idx = torch.randint(0, len(in_idx), (n, 2))
        same = pair_idx[:, 0] == pair_idx[:, 1]
        pair_idx[same, 1] = (pair_idx[same, 1] + 1) % len(in_idx)
        a = in_idx[pair_idx[:, 0]]
        b = in_idx[pair_idx[:, 1]]
        c_out = out_idx[torch.randint(0, len(out_idx), (n,))]
        gap_ab = torch.norm(embeddings[a] - embeddings[b], dim=-1)
        gap_ac = torch.norm(embeddings[a] - embeddings[c_out], dim=-1)
        gap_bc = torch.norm(embeddings[b] - embeddings[c_out], dim=-1)
        scores[c] = ((gap_ab < gap_ac) & (gap_ab < gap_bc)).float().mean().item()
    return scores


def evaluate(model: SigMLUnsupervised, loader, device: str) -> dict:
    """Evaluate model: per-level purity/witnessability, raise rates, effective depth."""
    model.eval()
    n_levels = len(model.levels)

    all_chi = [[] for _ in range(n_levels)]
    all_p = [[] for _ in range(n_levels)]
    all_z = [[] for _ in range(n_levels)]
    all_eval_labels = []

    with torch.no_grad():
        for images, eval_labels in loader:
            images = images.to(device)
            out = model(images)
            for i, lvl in enumerate(out["levels"]):
                all_chi[i].append(lvl["chi"].cpu())
                all_p[i].append(lvl["p"].cpu())
                all_z[i].append(lvl["z"].cpu())
            all_eval_labels.append(eval_labels)

    eval_labels = torch.cat(all_eval_labels)

    # Per-level metrics
    level_metrics = []
    for i in range(n_levels):
        chi = torch.cat(all_chi[i])
        p = torch.cat(all_p[i])
        z = torch.cat(all_z[i])

        assignments = p.argmax(dim=-1)
        k = p.shape[1]

        purity = cluster_purity(assignments, eval_labels)
        witness = ccd_witnessability(z, assignments, k)
        marginal = p.mean(0)

        level_metrics.append({
            "purity": purity,
            "mean_chi": chi.mean().item(),
            "witnessability": witness,
            "marginal": marginal,
            "chi": chi,
            "p": p,
            "z": z,
        })

    # Raise rates for consecutive pairs
    alive_indices = [i for i in range(n_levels) if model.levels[i].is_alive]
    raise_rates = {}

    for i in range(n_levels - 1):
        chi_lo = level_metrics[i]["chi"]
        chi_hi = level_metrics[i + 1]["chi"]
        raise_rates[f"raise_L{i}_{i+1}"] = raise_satisfaction_rate(chi_lo, chi_hi)

    # Overall chain: chi_0 < chi_1 < ... across all alive levels
    if len(alive_indices) >= 2:
        chain_ok = torch.ones(len(eval_labels), dtype=torch.bool)
        for j in range(len(alive_indices) - 1):
            lo = alive_indices[j]
            hi = alive_indices[j + 1]
            chain_ok &= level_metrics[hi]["chi"] > level_metrics[lo]["chi"]
        raise_rates["raise_all"] = chain_ok.float().mean().item()
    else:
        raise_rates["raise_all"] = 1.0  # trivially satisfied

    model.train()
    return {
        "level_metrics": level_metrics,
        "raise_rates": raise_rates,
        "effective_depth": len(alive_indices),
        "alive_levels": alive_indices,
        "eval_labels": eval_labels,
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

    n_levels = cfg.model.n_levels
    ks = cfg.model.k_per_level()

    print(f"\nTraining for {cfg.n_epochs} epochs")
    print(f"Levels: {n_levels}  k_per_level: {ks}")
    print(f"Prune threshold: {cfg.model.prune_threshold}, patience: {cfg.model.prune_patience}")
    print("No labels used during training.\n")

    # Build header
    level_cols = " ".join(f"{'L'+str(i):>4}" for i in range(n_levels))
    header = (
        f"{'ep':>3} | {'total':>6} {'contr':>6} {'raise':>6} "
        f"{'hier':>6} {'unif':>6} | "
        f"{'r_all':>5} | {level_cols} | {'dpth':>4}"
    )
    print(header)
    print("-" * len(header))

    best_purity = 0.0
    # Track per-level, per-prototype witnessability history
    witness_history: list[list[torch.Tensor]] = [[] for _ in range(n_levels)]

    warmup_epochs = max(1, cfg.n_epochs // 5)

    for epoch in range(1, cfg.n_epochs + 1):
        model.train()
        epoch_losses: dict[str, float] = {}
        n_batches = 0
        t0 = time.time()

        # Warmup: ramp contrast weight over first few epochs
        warmup_factor = min(1.0, epoch / warmup_epochs)
        loss_cfg = replace(cfg.loss, w_contrast=cfg.loss.w_contrast * warmup_factor)

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

        # Record witnessability history
        for i in range(n_levels):
            witness_history[i].append(
                metrics["level_metrics"][i]["witnessability"].cpu().clone()
            )

        # Prune each level's prototypes based on CCD₃ witnessability
        for i, lvl in enumerate(model.levels):
            if lvl.is_alive:
                lvl.proto.prune(
                    metrics["level_metrics"][i]["witnessability"],
                    cfg.model.prune_threshold,
                    cfg.model.prune_patience,
                )

        # Log
        eff_ks = [model.levels[i].effective_k for i in range(n_levels)]
        eff_k_str = " ".join(f"{ek:4d}" for ek in eff_ks)
        alive = metrics["alive_levels"]
        depth = metrics["effective_depth"]

        print(
            f"{epoch:3d} | "
            f"{epoch_losses.get('total', 0):6.3f} "
            f"{epoch_losses.get('contrast', 0):6.3f} "
            f"{epoch_losses.get('raise', 0):6.3f} "
            f"{epoch_losses.get('hierarchy', 0):6.3f} "
            f"{epoch_losses.get('uniform', 0):6.3f} | "
            f"{metrics['raise_rates'].get('raise_all', 1.0):5.3f} | "
            f"{eff_k_str} | "
            f"{depth:4d}"
        )

        # Save best model on finest-alive-level purity
        if alive:
            finest_purity = metrics["level_metrics"][alive[-1]]["purity"]
            if finest_purity > best_purity:
                best_purity = finest_purity
                torch.save({
                    "model_state_dict": model.state_dict(),
                    "model_config": cfg.model,
                    "loss_config": cfg.loss,
                    "epoch": epoch,
                    "metrics": {
                        "raise_rates": metrics["raise_rates"],
                        "effective_depth": depth,
                        "alive_levels": alive,
                        "level_purities": [
                            metrics["level_metrics"][i]["purity"]
                            for i in range(n_levels)
                        ],
                    },
                }, save_path)

    print(f"\nBest finest-level purity: {best_purity:.4f}")
    print(f"Saved to {save_path}")

    # ── Pruning diagnostics (CCD₃ witnessability) ──
    print("\n── PRUNING DIAGNOSTICS (CCD₃ witnessability) ──")
    print(f"  Threshold: {cfg.model.prune_threshold}  Patience: {cfg.model.prune_patience}")
    print(f"  (Random baseline ≈ 0.33; well-separated clusters > 0.8)")

    for i in range(n_levels):
        lvl = model.levels[i]
        alive_mask = lvl.proto.alive.cpu()
        n_alive = alive_mask.sum().item()
        n_total = len(alive_mask)
        is_dead = not lvl.is_alive

        if is_dead:
            print(f"\n  Level {i} — DEAD (0/{n_total} prototypes)")
            continue

        wit = torch.stack(witness_history[i])  # (n_epochs, k)
        final_wit = wit[-1]

        surviving = alive_mask.nonzero(as_tuple=True)[0]
        pruned = (~alive_mask).nonzero(as_tuple=True)[0]

        print(f"\n  Level {i} ({n_alive} alive / {n_total}):")

        # Surviving stats
        if len(surviving) > 0:
            final_surv = final_wit[surviving]
            print(f"    Surviving — wit min: {final_surv.min():.3f}  "
                  f"max: {final_surv.max():.3f}  mean: {final_surv.mean():.3f}  "
                  f"std: {final_surv.std():.3f}")

        # Pruned stats
        if len(pruned) > 0:
            pruned_peaks = wit[:, pruned].max(dim=0).values
            print(f"    Pruned ({len(pruned)}) — peak wit min: {pruned_peaks.min():.3f}  "
                  f"max: {pruned_peaks.max():.3f}  mean: {pruned_peaks.mean():.3f}")
            # Classify: never-grounded vs lost-grounding
            never_grounded = (pruned_peaks < cfg.model.prune_threshold).sum().item()
            lost_grounding = len(pruned) - never_grounded
            print(f"    Never grounded (peak < {cfg.model.prune_threshold}): {never_grounded}")
            print(f"    Lost grounding (had witnesses, then lost them): {lost_grounding}")
            if lost_grounding > 0:
                print("    → Genuine ontological compression: abstractions lost their ground")

            # Trajectories for most interesting pruned prototypes
            show_n = min(3, len(pruned))
            top_pruned = pruned_peaks.argsort(descending=True)[:show_n]
            if show_n > 0:
                print(f"    Top {show_n} pruned by peak witnessability:")
                for pi in top_pruned:
                    pid = pruned[pi].item()
                    traj = wit[:, pid].tolist()
                    # Show first 5, ..., last
                    if len(traj) > 7:
                        traj_parts = [f"{w:.2f}" for w in traj[:5]]
                        traj_parts.append("...")
                        traj_parts.append(f"{traj[-1]:.2f}")
                    else:
                        traj_parts = [f"{w:.2f}" for w in traj]
                    print(f"      proto {pid:3d}: {' → '.join(traj_parts)}")

    return save_path


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Train unsupervised significance model"
    )
    parser.add_argument("--n-epochs", type=int, default=30)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--n-levels", type=int, default=5)
    parser.add_argument("--k-min", type=int, default=8)
    parser.add_argument("--k-max", type=int, default=100)
    parser.add_argument("--device", type=str, default="")
    args = parser.parse_args()

    cfg = TrainConfig(
        n_epochs=args.n_epochs,
        lr=args.lr,
        device=args.device,
        data=DataConfig(batch_size=args.batch_size),
        model=ModelConfig(
            n_levels=args.n_levels,
            k_min=args.k_min,
            k_max=args.k_max,
        ),
    )
    train(cfg)


if __name__ == "__main__":
    main()
