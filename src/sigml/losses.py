"""Loss functions mapping to the Lean formalization.

Each loss corresponds to a piece of the formal structure:
  L_genus    → genus.pred (digit vs non-digit classification)
  L_diff     → differentia.pred (which digit, 10-way)
  L_raise    → isEssential: chi_G < chi_D on members
  L_contrast → SimilarByContrast: triplet loss on chi_D axes
  L_onehot   → exclusivity: exactly one differentia fires per digit
"""

from __future__ import annotations

import torch
import torch.nn.functional as F

from sigml.config import SigMLConfig


def genus_loss(logit_G: torch.Tensor, y_genus: torch.Tensor) -> torch.Tensor:
    """Binary cross-entropy for digit vs non-digit."""
    return F.binary_cross_entropy_with_logits(logit_G, y_genus)


def differentia_loss(
    logit_D: torch.Tensor, y_digit: torch.Tensor, mask_digit: torch.Tensor,
) -> torch.Tensor:
    """Cross-entropy over 10 differentia heads, only on digit images.

    Args:
        logit_D: [B, 10] differentia logits
        y_digit: [B] digit labels (0-9, -1 for non-digits)
        mask_digit: [B] boolean mask for digit images
    """
    if mask_digit.sum() == 0:
        return torch.tensor(0.0, device=logit_D.device)
    return F.cross_entropy(logit_D[mask_digit], y_digit[mask_digit])


def raise_loss(
    chi_G: torch.Tensor,
    chi_D: torch.Tensor,
    y_digit: torch.Tensor,
    mask_digit: torch.Tensor,
    margin: float = 1.0,
) -> torch.Tensor:
    """Raise constraint: chi_G < chi_D[true_digit] on digit images.

    Corresponds to isEssential: Raise(genus.chi a)(differentia.chi a)
    Enforced as hinge loss: max(0, margin + chi_G - chi_D_true).
    """
    if mask_digit.sum() == 0:
        return torch.tensor(0.0, device=chi_G.device)

    chi_G_d = chi_G[mask_digit]
    chi_D_d = chi_D[mask_digit]
    y_d = y_digit[mask_digit]

    # Gather the true differentia depth for each digit
    chi_D_true = chi_D_d.gather(1, y_d.unsqueeze(1)).squeeze(1)  # [N]

    return F.relu(margin + chi_G_d - chi_D_true).mean()


def contrast_loss(
    chi_D: torch.Tensor,
    y_digit: torch.Tensor,
    mask_digit: torch.Tensor,
    margin: float = 1.0,
) -> torch.Tensor:
    """Triplet contrast loss on differentia depth axes.

    Corresponds to SimilarByContrast:
      |chi_D_i(a) - chi_D_i(b)| < |chi_D_i(a) - chi_D_i(c)| (with margin)
      |chi_D_i(a) - chi_D_i(b)| < |chi_D_i(b) - chi_D_i(c)| (with margin)

    Triplets are mined within-batch: for each digit image (anchor),
    find a positive (same digit) and negative (different digit).
    """
    if mask_digit.sum() < 2:
        return torch.tensor(0.0, device=chi_D.device)

    chi_D_d = chi_D[mask_digit]          # [N, 10]
    y_d = y_digit[mask_digit]            # [N]
    N = y_d.size(0)

    # For each anchor, gather its true differentia axis score
    chi_true = chi_D_d.gather(1, y_d.unsqueeze(1)).squeeze(1)  # [N]

    total_loss = torch.tensor(0.0, device=chi_D.device)
    n_triplets = 0

    # Simple within-batch mining: for each anchor, find one pos and one neg
    for digit in range(10):
        pos_mask = y_d == digit
        neg_mask = y_d != digit
        n_pos = pos_mask.sum().item()
        n_neg = neg_mask.sum().item()
        if n_pos < 2 or n_neg < 1:
            continue

        pos_idx = pos_mask.nonzero(as_tuple=True)[0]
        neg_idx = neg_mask.nonzero(as_tuple=True)[0]

        # Use first as anchor, second as positive
        anchors = chi_true[pos_idx[:-1]]           # [n_pos-1]
        positives = chi_true[pos_idx[1:]]          # [n_pos-1]

        # Pick a random negative for each anchor (cycle through neg_idx)
        n_pairs = anchors.size(0)
        neg_sel = neg_idx[torch.arange(n_pairs, device=chi_D.device) % n_neg]
        negatives = chi_true[neg_sel]              # [n_pairs]

        d_ab = (anchors - positives).abs()
        d_ac = (anchors - negatives).abs()
        d_bc = (positives - negatives).abs()

        # SimilarByContrast: both gap inequalities
        loss1 = F.relu(margin + d_ab - d_ac)
        loss2 = F.relu(margin + d_ab - d_bc)

        total_loss = total_loss + (loss1 + loss2).sum()
        n_triplets += n_pairs

    if n_triplets == 0:
        return torch.tensor(0.0, device=chi_D.device)
    return total_loss / n_triplets


def onehot_loss(
    logit_D: torch.Tensor, mask_digit: torch.Tensor,
) -> torch.Tensor:
    """Exclusivity: exactly one differentia should fire per digit image.

    Penalty: (sum(sigmoid(logit_D)) - 1)^2 on digit images.
    """
    if mask_digit.sum() == 0:
        return torch.tensor(0.0, device=logit_D.device)
    probs = torch.sigmoid(logit_D[mask_digit])  # [N, 10]
    return ((probs.sum(dim=1) - 1.0) ** 2).mean()


def total_loss(
    logit_G: torch.Tensor,
    chi_G: torch.Tensor,
    logit_D: torch.Tensor,
    chi_D: torch.Tensor,
    y_genus: torch.Tensor,
    y_digit: torch.Tensor,
    config: SigMLConfig,
) -> tuple[torch.Tensor, dict[str, float]]:
    """Compute weighted sum of all losses.

    Returns (total_loss, dict of individual loss values for logging).
    """
    mask_digit = y_genus > 0.5

    l_gen = genus_loss(logit_G, y_genus)
    l_diff = differentia_loss(logit_D, y_digit, mask_digit)
    l_raise = raise_loss(chi_G, chi_D, y_digit, mask_digit, config.raise_margin)
    l_con = contrast_loss(chi_D, y_digit, mask_digit, config.contrast_margin)
    l_oh = onehot_loss(logit_D, mask_digit)

    total = (
        config.w_genus * l_gen
        + config.w_diff * l_diff
        + config.w_raise * l_raise
        + config.w_contrast * l_con
        + config.w_onehot * l_oh
    )

    details = {
        "genus": l_gen.item(),
        "diff": l_diff.item(),
        "raise": l_raise.item(),
        "contrast": l_con.item(),
        "onehot": l_oh.item(),
        "total": total.item(),
    }
    return total, details
