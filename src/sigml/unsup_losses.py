"""
losses.py — Unsupervised losses for N-level hierarchy, mapping to the Lean formalization.

NO labels are used anywhere in this file. Cluster identities are discovered
from the model's own soft assignments. The Lean structure dictates the loss:

  L_contrast  <->  CCD3 at each alive level (SimilarByContrast)
  L_raise     <->  Raise composition across all adjacent level pairs
                   (chi_0 < chi_1 < ... < chi_{L-1})
  L_hier      <->  Each finer level predicts its parent
                   (definiendum = genus.meet differentia, composed via chain)
  L_uniform   <->  no_universal_ccd + collapse prevention per level

Total loss: L = w_contrast * L_contrast + w_raise * L_raise
             + w_hier * L_hier + w_unif * L_uniform

Key design decision: the contrast losses use SOFT cluster assignments as
pseudo-labels for triplet mining. An image is an "anchor/positive" for
cluster k if its assignment probability p[k] > threshold. This makes the
mining differentiable and label-free.
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass


@dataclass
class LossConfig:
    # Contrast losses
    contrast_margin: float = 1.0
    contrast_threshold: float = 0.3   # min prob to count as cluster member
    max_triplets: int = 256           # triplets to mine per batch per cluster

    # Raise loss
    raise_margin: float = 1.0        # enforces chi_{i+1} > chi_i + margin

    # Loss weights
    w_contrast: float = 1.0   # applied per alive level, averaged
    w_raise: float = 1.0
    w_hier: float = 0.5
    w_unif: float = 2.0       # strong anti-collapse


def _soft_triplet_loss(
    z: torch.Tensor,          # (B, dim) embeddings
    p: torch.Tensor,          # (B, k) soft cluster assignments
    margin: float,
    threshold: float,
    max_triplets: int,
) -> torch.Tensor:
    """
    Unsupervised triplet loss using hard cluster assignments for mining,
    soft distances for gradients.

    For each cluster k (by argmax assignment):
      - Positives: images assigned to cluster k
      - Negatives: images assigned to any other cluster

    Lean analogue:
      Each satisfied triplet is an empirical CCDWitness3:
        a, b = two images from the same cluster (inside the concept)
        c    = an image from the contrast cluster (outside the concept)
    """
    B, k = p.shape
    device = z.device
    losses = []

    # Hard cluster assignments for mining
    assignments = p.argmax(dim=-1)  # (B,)

    # Pairwise L2 distances in embedding space
    dist = torch.cdist(z, z, p=2)  # (B, B)

    for cluster_idx in range(k):
        pos_mask = assignments == cluster_idx
        neg_mask = assignments != cluster_idx

        n_pos = pos_mask.sum().item()
        n_neg = neg_mask.sum().item()

        if n_pos < 2 or n_neg < 1:
            continue

        pos_idx = pos_mask.nonzero(as_tuple=True)[0]
        neg_idx = neg_mask.nonzero(as_tuple=True)[0]

        # Sample triplets
        n_triplets = min(max_triplets, n_pos - 1)
        if n_triplets == 0:
            continue

        # Random anchor-positive pairs within cluster
        pairs = torch.randint(0, n_pos, (n_triplets, 2), device=device)
        same = pairs[:, 0] == pairs[:, 1]
        pairs[same, 1] = (pairs[same, 1] + 1) % n_pos

        anchors = pos_idx[pairs[:, 0]]
        positives = pos_idx[pairs[:, 1]]
        negatives = neg_idx[torch.randint(0, n_neg, (n_triplets,), device=device)]

        d_ap = dist[anchors, positives]   # Gap(a, b)
        d_an = dist[anchors, negatives]   # Gap(a, c)
        d_pn = dist[positives, negatives] # Gap(b, c)

        # SimilarByContrast: both gap inequalities
        loss_ac = F.relu(margin + d_ap - d_an)
        loss_bc = F.relu(margin + d_ap - d_pn)
        losses.append((loss_ac + loss_bc).mean())

    if not losses:
        return torch.tensor(0.0, device=device, requires_grad=True)
    return torch.stack(losses).mean()


def loss_contrast(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """
    CCD3 at each alive level, averaged.

    Lean: SimilarByContrast at each level of the hierarchy.
    """
    device = out["z"].device
    details = {}
    values = []

    for i, lvl in enumerate(out["levels"]):
        if not lvl["alive"]:
            continue
        L = _soft_triplet_loss(
            z=lvl["z"], p=lvl["p"],
            margin=cfg.contrast_margin,
            threshold=cfg.contrast_threshold,
            max_triplets=cfg.max_triplets,
        )
        details[f"contrast_L{i}"] = L.item()
        values.append(L)

    if not values:
        return torch.tensor(0.0, device=device, requires_grad=True), details
    avg = torch.stack(values).mean()
    return avg, details


def loss_raise(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """
    Raise: chi_i < chi_{i+1} for all adjacent level pairs.

    Computed for ALL pairs (not just alive) since chi values are always
    valid — the depth linear layer produces output regardless of prototype
    aliveness. This keeps the depth ordering intact even for dead levels.

    Lean: SignificanceRaise.compose — depth increases at each level.
    """
    device = out["z"].device
    levels = out["levels"]
    n = len(levels)
    details = {}
    values = []

    for i in range(n - 1):
        chi_lo = levels[i]["chi"]
        chi_hi = levels[i + 1]["chi"]
        L = F.relu(cfg.raise_margin + chi_lo - chi_hi).mean()
        details[f"raise_L{i}_{i+1}"] = L.item()
        values.append(L)

    if not values:
        return torch.tensor(0.0, device=device, requires_grad=True), details
    avg = torch.stack(values).mean()
    return avg, details


def loss_hierarchy(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """
    Hierarchy: finer level predicts coarser level.

    H(p_i | p_{i+1}) for each adjacent pair where both are alive —
    the conditional entropy of the coarser level given the finer level
    should be low.

    Lean: definiendum = genus.meet differentia, composed via KonceptDef.chain.
    """
    device = out["z"].device
    levels = out["levels"]
    n = len(levels)
    details = {}
    values = []

    for i in range(n - 1):
        if not levels[i]["alive"] or not levels[i + 1]["alive"]:
            continue

        p_coarse = levels[i]["p"]      # (B, k_i)
        p_fine = levels[i + 1]["p"]    # (B, k_{i+1})

        # For each fine cluster, compute the expected coarse distribution
        joint = p_fine.T @ p_coarse                          # (k_{i+1}, k_i)
        joint = joint / (joint.sum(dim=-1, keepdim=True) + 1e-8)

        # Entropy of coarse given each fine cluster — should be low
        entropy = -(joint * (joint + 1e-8).log()).sum(dim=-1)  # (k_{i+1},)

        # Weight by how much each fine cluster is used
        fine_usage = p_fine.mean(dim=0)   # (k_{i+1},)
        L = (fine_usage * entropy).sum()
        details[f"hier_L{i}_{i+1}"] = L.item()
        values.append(L)

    if not values:
        return torch.tensor(0.0, device=device, requires_grad=True), details
    avg = torch.stack(values).mean()
    return avg, details


def loss_uniform(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """
    Anti-collapse: no single cluster absorbs everything, per alive level.

    Lean: no_universal_ccd — a universal concept cannot be CCD-grounded.
    """
    device = out["z"].device
    details = {}
    values = []

    for i, lvl in enumerate(out["levels"]):
        if not lvl["alive"]:
            continue
        marginal = lvl["p"].mean(dim=0)
        L = marginal.max()
        details[f"unif_L{i}"] = L.item()
        values.append(L)

    if not values:
        return torch.tensor(0.0, device=device, requires_grad=True), details
    avg = torch.stack(values).mean()
    return avg, details


def total_loss(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """Compute all losses and return their weighted sum plus breakdown."""
    L_c, d_c = loss_contrast(out, cfg)
    L_r, d_r = loss_raise(out, cfg)
    L_h, d_h = loss_hierarchy(out, cfg)
    L_u, d_u = loss_uniform(out, cfg)

    total = (
        cfg.w_contrast * L_c +
        cfg.w_raise * L_r +
        cfg.w_hier * L_h +
        cfg.w_unif * L_u
    )

    breakdown = {
        "contrast": L_c.item(),
        "raise": L_r.item(),
        "hierarchy": L_h.item(),
        "uniform": L_u.item(),
        "total": total.item(),
    }
    breakdown.update(d_c)
    breakdown.update(d_r)
    breakdown.update(d_h)
    breakdown.update(d_u)

    return total, breakdown
