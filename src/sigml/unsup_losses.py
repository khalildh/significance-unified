"""
losses.py — Five unsupervised losses mapping to the Lean formalization.

NO labels are used anywhere in this file. Cluster identities are discovered
from the model's own soft assignments (p_G, p_D). The Lean structure dictates
the loss design:

  L_genus_contrast   <->  CCD3 at the genus level
                         (SimilarByContrast for genus-level grouping)
  L_diff_contrast    <->  CCD3 at the differentia level
                         (SimilarByContrast within genus, contrasted across genus)
  L_raise            <->  KonceptDef.isEssential
                         (Raise: chi_G < chi_D on every image)
  L_hier             <->  definiendum = genus.meet differentia
                         (differentia assignment determines genus assignment)
  L_uniform          <->  no_universal_ccd + collapse prevention
                         (no cluster absorbs everything)

Total loss: L = L_genus_contrast + L_diff_contrast + L_raise + L_hier + L_uniform

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
    contrast_threshold: float = 0.3   # min prob to count as cluster member (lower = more triplets)
    max_triplets: int = 256           # triplets to mine per batch per cluster

    # Raise loss
    raise_margin: float = 1.0        # enforces chi_D > chi_G + margin

    # Hierarchy loss weight
    hier_weight: float = 1.0

    # Uniformity loss weight (collapse prevention)
    uniform_weight: float = 0.5

    # Loss weights
    w_genus: float = 1.0
    w_diff:  float = 1.0
    w_raise: float = 1.0
    w_hier:  float = 0.5
    w_unif:  float = 2.0             # strong anti-collapse


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

    The loss encourages |z_a - z_p| < |z_a - z_n| - margin,
    which is the soft version of SimilarByContrast:
      Gap(a, b) < Gap(a, c)  and  Gap(a, b) < Gap(b, c)

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


def loss_genus_contrast(out: dict, cfg: LossConfig) -> torch.Tensor:
    """
    CCD3 at the genus level.

    Two images belong together at the genus level if they share a genus cluster.
    The contrast comes from a different genus cluster.

    Lean: SimilarByContrast(chi_G(a), chi_G(b), chi_G(c))
    where a, b share a genus, c does not.

    What this discovers: the top-level grouping of all images
    (e.g., "digit-like" vs "clothing-like" without being told which is which).
    """
    return _soft_triplet_loss(
        z=out["z_G"],
        p=out["p_G"],
        margin=cfg.contrast_margin,
        threshold=cfg.contrast_threshold,
        max_triplets=cfg.max_triplets,
    )


def loss_diff_contrast(out: dict, cfg: LossConfig) -> torch.Tensor:
    """
    CCD3 at the differentia level.

    Two images belong together at the differentia level if they share a
    differentia cluster. The contrast comes from a different differentia cluster.

    Lean: SimilarByContrast(chi_D(a), chi_D(b), chi_D(c))
    where a, b share a differentia, c is in a different differentia cluster
    (but may share the genus -- that's the within-genus contrast).

    What this discovers: the sub-groupings within each genus cluster
    (e.g., the 10 digit types, without being told there are 10).
    """
    return _soft_triplet_loss(
        z=out["z_D"],
        p=out["p_D"],
        margin=cfg.contrast_margin,
        threshold=cfg.contrast_threshold,
        max_triplets=cfg.max_triplets,
    )


def loss_raise(out: dict, cfg: LossConfig) -> torch.Tensor:
    """
    Raise: chi_G < chi_D on every image.

    This is the directed depth ordering -- differentia must be strictly
    deeper than genus.

    Lean: KonceptDef.isEssential: forall a, Raise (genus.chi a) (differentia.chi a)
    """
    chi_G = out["chi_G"]
    chi_D = out["chi_D"]
    return F.relu(cfg.raise_margin + chi_G - chi_D).mean()


def loss_hierarchy(out: dict, cfg: LossConfig) -> torch.Tensor:
    """
    Hierarchy: differentia assignment determines genus assignment.

    The definiendum is the meet of genus and differentia:
      definiendum = genus AND differentia

    Implemented as: minimize H(p_G | p_D) -- the conditional entropy of
    genus assignment given differentia assignment.

    Lean: definiendum = genus.meet differentia
    """
    p_G = out["p_G"]   # (B, k_genus)
    p_D = out["p_D"]   # (B, k_diff)

    # For each differentia cluster d, compute the expected genus distribution
    joint = p_D.T @ p_G                    # (k_diff, k_genus)
    joint = joint / (joint.sum(dim=-1, keepdim=True) + 1e-8)

    # Entropy of genus given each differentia cluster -- should be low
    entropy = -(joint * (joint + 1e-8).log()).sum(dim=-1)  # (k_diff,)

    # Weight by how much each differentia cluster is used
    diff_usage = p_D.mean(dim=0)   # (k_diff,)
    return (diff_usage * entropy).sum()


def loss_uniform(out: dict, cfg: LossConfig) -> torch.Tensor:
    """
    Uniformity: no cluster absorbs everything.

    Lean: no_universal_ccd -- a universal concept cannot be CCD-grounded.

    We prevent collapse by maximizing the entropy of the marginal cluster
    assignment distribution.
    """
    # Genus marginal
    p_G_marginal = out["p_G"].mean(dim=0)
    H_G = -(p_G_marginal * (p_G_marginal + 1e-8).log()).sum()

    # Differentia marginal
    p_D_marginal = out["p_D"].mean(dim=0)
    H_D = -(p_D_marginal * (p_D_marginal + 1e-8).log()).sum()

    # Maximize entropy -> minimize negative entropy
    return -(H_G + H_D)


def total_loss(out: dict, cfg: LossConfig) -> tuple[torch.Tensor, dict]:
    """Compute all five losses and return their weighted sum plus breakdown."""
    L_gc = loss_genus_contrast(out, cfg)
    L_dc = loss_diff_contrast(out, cfg)
    L_r  = loss_raise(out, cfg)
    L_h  = loss_hierarchy(out, cfg)
    L_u  = loss_uniform(out, cfg)

    total = (
        cfg.w_genus * L_gc +
        cfg.w_diff  * L_dc +
        cfg.w_raise * L_r  +
        cfg.w_hier  * L_h  +
        cfg.w_unif  * L_u
    )

    breakdown = {
        "genus_contrast": L_gc.item(),
        "diff_contrast":  L_dc.item(),
        "raise":          L_r.item(),
        "hierarchy":      L_h.item(),
        "uniform":        L_u.item(),
        "total":          total.item(),
    }

    return total, breakdown
