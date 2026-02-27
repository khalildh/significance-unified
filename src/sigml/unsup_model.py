"""
model.py — Two-level structured encoder for unsupervised significance learning.

Architecture:
  image → CNN encoder → shared representation z ∈ ℝ^embed_dim
                       ↓
          ┌────────────┴────────────┐
     Genus head               Differentia head
   z_G ∈ ℝ^genus_dim        z_D ∈ ℝ^diff_dim
   χ_G ∈ ℝ  (depth)         χ_D ∈ ℝ  (depth)
   p_G ∈ Δ^{k_G} (soft)     p_D ∈ Δ^{k_D} (soft)

The model has NO classification heads. Cluster assignments emerge from
the embeddings via a learned prototype layer (soft nearest-neighbour
to k learned centroids). No labels are used anywhere.

Lean analogue:
  z_G  →  genus.χ (the characteristic, as a vector before projection)
  χ_G  →  genus depth scalar
  p_G  →  soft genus.pred (which genus cluster does this belong to?)
  z_D  →  differentia.χ
  χ_D  →  differentia depth scalar
  p_D  →  soft differentia.pred
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass


@dataclass
class ModelConfig:
    embed_dim: int = 128      # shared CNN output dim
    genus_dim: int = 64       # genus embedding dim
    diff_dim: int = 64        # differentia embedding dim
    k_genus: int = 4          # number of genus clusters to discover
    k_diff: int = 20          # number of differentia clusters to discover
                              # (deliberately over-specified; unused clusters
                              #  collapse under the uniformity loss)
    temp: float = 0.5         # softmax temperature for soft assignments (higher = softer)


class CNNEncoder(nn.Module):
    """Shared visual encoder — same architecture as original sigml."""

    def __init__(self, embed_dim: int):
        super().__init__()
        self.net = nn.Sequential(
            # Block 1
            nn.Conv2d(1, 32, 3, padding=1),
            nn.BatchNorm2d(32),
            nn.ReLU(),
            nn.MaxPool2d(2),          # 28 → 14
            # Block 2
            nn.Conv2d(32, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(),
            nn.MaxPool2d(2),          # 14 → 7
            # Flatten
            nn.Flatten(),
            nn.Linear(64 * 7 * 7, embed_dim),
            nn.ReLU(),
        )

    def forward(self, x):
        return self.net(x)


class PrototypeLayer(nn.Module):
    """
    Soft assignment to k learned prototypes via temperature-scaled cosine sim.

    Returns:
      probs: (B, k)  soft cluster assignment probabilities

    This is the differentiable analogue of 'which concept does this fall under?'
    The prototypes are the concept centroids; the assignment is soft pred.
    """

    def __init__(self, dim: int, k: int, temp: float):
        super().__init__()
        self.prototypes = nn.Parameter(torch.randn(k, dim))
        self.temp = temp

    def forward(self, z: torch.Tensor) -> torch.Tensor:
        z_norm = F.normalize(z, dim=-1)
        p_norm = F.normalize(self.prototypes, dim=-1)
        sim = z_norm @ p_norm.T          # (B, k)
        return F.softmax(sim / self.temp, dim=-1)


class SigMLUnsupervised(nn.Module):
    """
    Full two-level significance model.

    forward() returns a dict with all heads needed by the losses.
    No labels are used or expected.
    """

    def __init__(self, cfg: ModelConfig):
        super().__init__()
        self.cfg = cfg

        # Shared encoder
        self.encoder = CNNEncoder(cfg.embed_dim)

        # Genus head
        self.genus_proj = nn.Linear(cfg.embed_dim, cfg.genus_dim)
        self.genus_depth = nn.Linear(cfg.embed_dim, 1)
        self.genus_proto = PrototypeLayer(cfg.genus_dim, cfg.k_genus, cfg.temp)

        # Differentia head
        self.diff_proj = nn.Linear(cfg.embed_dim, cfg.diff_dim)
        self.diff_depth = nn.Linear(cfg.embed_dim, 1)
        self.diff_proto = PrototypeLayer(cfg.diff_dim, cfg.k_diff, cfg.temp)

    def forward(self, x: torch.Tensor) -> dict:
        z = self.encoder(x)                          # (B, embed_dim)

        # Genus
        z_G = self.genus_proj(z)                     # (B, genus_dim)
        chi_G = self.genus_depth(z).squeeze(-1)      # (B,)
        p_G = self.genus_proto(z_G)                  # (B, k_genus)

        # Differentia
        z_D = self.diff_proj(z)                      # (B, diff_dim)
        chi_D = self.diff_depth(z).squeeze(-1)       # (B,)
        p_D = self.diff_proto(z_D)                   # (B, k_diff)

        return {
            "z": z,
            "z_G": z_G, "chi_G": chi_G, "p_G": p_G,
            "z_D": z_D, "chi_D": chi_D, "p_D": p_D,
        }
