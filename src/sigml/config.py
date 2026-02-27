"""Hyperparameter configuration for the Significance ML experiment."""

from __future__ import annotations

from dataclasses import dataclass

import torch


def default_device() -> str:
    """Return the best available device: cuda > mps > cpu."""
    if torch.cuda.is_available():
        return "cuda"
    if torch.backends.mps.is_available():
        return "mps"
    return "cpu"


@dataclass
class SigMLConfig:
    """All hyperparameters for the significance-ML MNIST experiment.

    Mirrors the Lean formalization:
      - One shared genus (digit vs non-digit)
      - Ten differentiae (one per digit class)
      - Raise: differentia depth > genus depth on members
      - Contrast: SimilarByContrast triplets on each differentia axis
    """

    # Architecture
    encoder_channels: list[int] | None = None  # CNN channels per conv block
    encoder_fc_dim: int = 128                  # FC layer after conv
    n_diff: int = 10                           # number of differentiae (digit classes)

    # Training
    batch_size: int = 256
    n_epochs: int = 10
    lr: float = 3e-4
    weight_decay: float = 1e-5

    # Loss weights
    w_genus: float = 1.0       # genus classification (digit vs non-digit)
    w_diff: float = 1.0        # differentia classification (which digit)
    w_raise: float = 0.5       # Raise constraint: chi_diff > chi_genus on members
    w_contrast: float = 1.0    # triplet contrast loss on chi_diff axes
    w_onehot: float = 0.5      # exclusivity: exactly one differentia fires

    # Margins
    raise_margin: float = 1.0     # margin for Raise constraint
    contrast_margin: float = 1.0  # margin for triplet contrast

    # Data
    seed: int = 42

    def __post_init__(self) -> None:
        if self.encoder_channels is None:
            self.encoder_channels = [32, 64]
