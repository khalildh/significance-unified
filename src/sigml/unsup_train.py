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
    model.eval()

    all_chi_G, all_chi_D = [], []
    all_p_G, all_p_D = [], []
    all_z_G, all_z_D = [], []
    all_eval_labels = []

    with torch.no_grad():
        for images, eval_labels in loader:
            images = images.to(device)
            out = model(images)
            all_chi_G.append(out["chi_G"].cpu())
            all_chi_D.append(out["chi_D"].cpu())
            all_p_G.append(out["p_G"].cpu())
            all_p_D.append(out["p_D"].cpu())
            all_z_G.append(out["z_G"].cpu())
            all_z_D.append(out["z_D"].cpu())
            all_eval_labels.append(eval_labels)

    chi_G = torch.cat(all_chi_G)
    chi_D = torch.cat(all_chi_D)
    p_G = torch.cat(all_p_G)
    p_D = torch.cat(all_p_D)
    z_G = torch.cat(all_z_G)
    z_D = torch.cat(all_z_D)
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

    # CCD₃ witnessability per cluster (pruning signal)
    k_genus = p_G.shape[1]
    k_diff = p_D.shape[1]
    genus_witness = ccd_witnessability(z_G, genus_assignments, k_genus)
    diff_witness = ccd_witnessability(z_D, diff_assignments, k_diff)

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
        "genus_marginal": p_G.mean(0),
        "diff_marginal": p_D.mean(0),
        "genus_witnessability": genus_witness,   # (k_genus,) CCD₃ scores
        "diff_witnessability": diff_witness,     # (k_diff,) CCD₃ scores
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
    print(f"Genus clusters (overcomplete): {cfg.model.k_genus}")
    print(f"Differentia clusters (overcomplete): {cfg.model.k_diff}")
    print(f"Prune threshold: {cfg.model.prune_threshold}, patience: {cfg.model.prune_patience}")
    print("No labels used during training.\n")

    header = (
        f"{'ep':>3} | {'total':>6} {'gc':>6} {'dc':>6} "
        f"{'raise':>6} {'hier':>6} {'unif':>6} | "
        f"{'r_rate':>6} {'g_pur':>6} {'d_pur':>6} | "
        f"{'effG':>4} {'effD':>4} | "
        f"{'chi_G':>6} {'chi_D':>6} {'gap':>6}"
    )
    print(header)
    print("-" * len(header))

    best_diff_purity = 0.0
    # Track per-prototype witnessability history for pruning diagnostics
    genus_witness_history: list[torch.Tensor] = []
    diff_witness_history: list[torch.Tensor] = []

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
        genus_witness_history.append(metrics["genus_witnessability"].cpu().clone())
        diff_witness_history.append(metrics["diff_witnessability"].cpu().clone())

        # Prune prototypes that can't produce CCD₃ witnesses
        model.genus_proto.prune(
            metrics["genus_witnessability"],
            cfg.model.prune_threshold,
            cfg.model.prune_patience,
        )
        model.diff_proto.prune(
            metrics["diff_witnessability"],
            cfg.model.prune_threshold,
            cfg.model.prune_patience,
        )

        eff_g = model.genus_proto.effective_k
        eff_d = model.diff_proto.effective_k

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
            f"{eff_g:4d} "
            f"{eff_d:4d} | "
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

    # ── Pruning diagnostics (CCD₃ witnessability) ──
    g_wit = torch.stack(genus_witness_history)  # (n_epochs, k_genus)
    d_wit = torch.stack(diff_witness_history)   # (n_epochs, k_diff)
    g_alive = model.genus_proto.alive.cpu()
    d_alive = model.diff_proto.alive.cpu()

    print("\n── PRUNING DIAGNOSTICS (CCD₃ witnessability) ──")
    print(f"  Threshold: {cfg.model.prune_threshold}  Patience: {cfg.model.prune_patience}")
    print(f"  (Random baseline ≈ 0.33; well-separated clusters > 0.8)")

    # Genus witnessability
    final_g = g_wit[-1]
    print(f"\n  Genus ({g_alive.sum()} alive / {len(g_alive)}):")
    sorted_g, idx_g = final_g.sort(descending=True)
    for i in range(len(sorted_g)):
        pid = idx_g[i].item()
        status = "alive" if g_alive[pid] else "DEAD"
        peak = g_wit[:, pid].max().item()
        final = sorted_g[i].item()
        traj = [f"{g_wit[e, pid]:.2f}" for e in range(min(5, len(g_wit)))]
        if len(g_wit) > 5:
            traj.append("...")
            traj.append(f"{final:.2f}")
        print(f"    proto {pid:2d}: wit={final:.3f}  peak={peak:.3f}  "
              f"[{status}]  [{' → '.join(traj)}]")

    # Differentia witnessability
    pruned_d = (~d_alive).nonzero(as_tuple=True)[0]
    surviving_d = d_alive.nonzero(as_tuple=True)[0]
    print(f"\n  Differentia ({d_alive.sum()} alive / {len(d_alive)}):")

    if len(surviving_d) > 0:
        final_surv = d_wit[-1, surviving_d]
        print(f"    Surviving — wit min: {final_surv.min():.3f}  "
              f"max: {final_surv.max():.3f}  mean: {final_surv.mean():.3f}  "
              f"std: {final_surv.std():.3f}")

    if len(pruned_d) > 0:
        pruned_peaks = d_wit[:, pruned_d].max(dim=0).values
        final_pruned = d_wit[-1, pruned_d]
        print(f"    Pruned ({len(pruned_d)}) — peak wit min: {pruned_peaks.min():.3f}  "
              f"max: {pruned_peaks.max():.3f}  mean: {pruned_peaks.mean():.3f}")
        # Classify: never-grounded vs lost-grounding
        never_grounded = (pruned_peaks < cfg.model.prune_threshold).sum().item()
        lost_grounding = len(pruned_d) - never_grounded
        print(f"    Never grounded (peak < {cfg.model.prune_threshold}): {never_grounded}")
        print(f"    Lost grounding (had witnesses, then lost them): {lost_grounding}")
        if lost_grounding > 0:
            print("    → Genuine ontological compression: abstractions lost their ground")

        # Show trajectories for most interesting pruned heads
        show_n = min(5, len(pruned_d))
        top_pruned = pruned_peaks.argsort(descending=True)[:show_n]
        print(f"\n  Top {show_n} pruned prototypes by peak witnessability:")
        for pi in top_pruned:
            pid = pruned_d[pi].item()
            traj = d_wit[:, pid].tolist()
            traj_str = " → ".join(f"{w:.2f}" for w in traj)
            print(f"    proto {pid:3d}: {traj_str}")
    else:
        print("  No prototypes pruned.")

    return save_path


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Train unsupervised significance model"
    )
    parser.add_argument("--n-epochs", type=int, default=30)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--lr", type=float, default=3e-4)
    parser.add_argument("--k-genus", type=int, default=16)
    parser.add_argument("--k-diff", type=int, default=100)
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
