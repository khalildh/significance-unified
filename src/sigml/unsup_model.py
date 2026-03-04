"""
model.py — N-level hierarchical encoder for unsupervised significance learning.

Architecture:
  image → CNN encoder → shared representation z ∈ ℝ^embed_dim
                       ↓
          ┌──── Level 0 (most general) ────┐
          │  z_0 ∈ ℝ^level_dim             │
          │  χ_0 ∈ ℝ  (depth)              │
          │  p_0 ∈ Δ^{k_0} (soft)          │
          └────────────────────────────────┘
                      ...
          ┌──── Level L-1 (most specific) ─┐
          │  z_{L-1} ∈ ℝ^level_dim         │
          │  χ_{L-1} ∈ ℝ  (depth)          │
          │  p_{L-1} ∈ Δ^{k_{L-1}} (soft)  │
          └────────────────────────────────┘

The model has NO classification heads. Cluster assignments emerge from
the embeddings via learned prototype layers (soft nearest-neighbour
to k learned centroids). No labels are used anywhere.

Both width (prototypes per level) and depth (number of alive levels)
are discovered via overcomplete initialization + CCD₃ witnessability pruning.

Lean analogue:
  Raise is transitive (SignificanceRaise.compose), definition chains
  compose (KonceptDef.chain), depth accumulates (chain_depth_bound).
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass


@dataclass
class ModelConfig:
    embed_dim: int = 128      # shared CNN output dim
    n_levels: int = 5         # overcomplete depth (pruned during training)
    level_dim: int = 64       # embedding dim per level (shared)
    k_min: int = 8            # prototypes at level 0 (most general)
    k_max: int = 100          # prototypes at level L-1 (most specific)
    temp: float = 0.5         # softmax temperature for soft assignments
    prune_threshold: float = 0.5    # min CCD₃ witnessability to stay alive
    prune_patience: int = 3         # consecutive epochs below threshold before pruning

    def k_per_level(self) -> list[int]:
        """Geometric progression from k_min to k_max."""
        if self.n_levels == 1:
            return [self.k_min]
        ratio = (self.k_max / self.k_min) ** (1.0 / (self.n_levels - 1))
        ks = [max(1, round(self.k_min * ratio**i)) for i in range(self.n_levels)]
        ks[-1] = self.k_max  # force exact
        return ks


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

    Supports overcomplete initialization with pruning: prototypes whose
    CCD₃ witnessability stays below threshold for patience epochs are
    marked dead and excluded from softmax (set to -inf).
    """

    def __init__(self, dim: int, k: int, temp: float):
        super().__init__()
        self.prototypes = nn.Parameter(torch.randn(k, dim))
        self.temp = temp
        self.register_buffer("alive", torch.ones(k, dtype=torch.bool))
        self.register_buffer("dead_epochs", torch.zeros(k, dtype=torch.long))

    def forward(self, z: torch.Tensor) -> torch.Tensor:
        z_norm = F.normalize(z, dim=-1)
        p_norm = F.normalize(self.prototypes, dim=-1)
        sim = z_norm @ p_norm.T          # (B, k)
        # Mask dead prototypes so they get zero probability after softmax
        sim = sim.masked_fill(~self.alive.unsqueeze(0), float("-inf"))
        return F.softmax(sim / self.temp, dim=-1)

    def prune(self, mean_mass: torch.Tensor, threshold: float, patience: int) -> None:
        """Update dead_epochs and mark prototypes dead when patience exhausted."""
        below = mean_mass.to(self.alive.device) < threshold
        self.dead_epochs[self.alive & below] += 1
        self.dead_epochs[self.alive & ~below] = 0
        newly_dead = self.alive & (self.dead_epochs >= patience)
        if newly_dead.any():
            self.alive[newly_dead] = False

    @property
    def effective_k(self) -> int:
        return int(self.alive.sum().item())


class HierarchyLevel(nn.Module):
    """One level of the concept hierarchy: projection + depth + prototype layer.

    Lean analogue: one step in a KonceptDef.chain — a concept at a
    particular depth with its own characteristic function and predicate.
    """

    def __init__(self, embed_dim: int, level_dim: int, k: int, temp: float):
        super().__init__()
        self.proj = nn.Linear(embed_dim, level_dim)
        self.depth = nn.Linear(embed_dim, 1)
        self.proto = PrototypeLayer(level_dim, k, temp)

    def forward(self, z: torch.Tensor) -> dict:
        z_proj = self.proj(z)                    # (B, level_dim)
        chi = self.depth(z).squeeze(-1)          # (B,)
        p = self.proto(z_proj)                   # (B, k)
        return {"z": z_proj, "chi": chi, "p": p}

    @property
    def effective_k(self) -> int:
        return self.proto.effective_k

    @property
    def is_alive(self) -> bool:
        return self.effective_k > 0


class SigMLUnsupervised(nn.Module):
    """
    N-level hierarchical significance model.

    forward() returns a dict with all levels needed by the losses.
    No labels are used or expected.

    Lean analogue: a chain of KonceptDefs with Raise composing across
    levels and CCD₃ witnessability pruning determining which levels survive.
    """

    def __init__(self, cfg: ModelConfig):
        super().__init__()
        self.cfg = cfg
        self.encoder = CNNEncoder(cfg.embed_dim)
        self.levels = nn.ModuleList([
            HierarchyLevel(cfg.embed_dim, cfg.level_dim, k, cfg.temp)
            for k in cfg.k_per_level()
        ])

    def forward(self, x: torch.Tensor) -> dict:
        z = self.encoder(x)                      # (B, embed_dim)
        level_outs = []
        for lvl in self.levels:
            out = lvl(z)
            out["alive"] = lvl.is_alive
            out["effective_k"] = lvl.effective_k
            level_outs.append(out)
        return {
            "z": z,
            "n_levels": len(self.levels),
            "levels": level_outs,
        }
