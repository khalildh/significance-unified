"""Model: shared CNN encoder with genus + differentia heads.

Mirrors the Lean formalization:
  - genus head: pred_G (is digit?) + chi_G (genus depth)
  - differentia heads: pred_D[0..9] (has differentia i?) + chi_D[0..9] (diff depth)
"""

from __future__ import annotations

import torch
import torch.nn as nn
import torch.nn.functional as F

from sigml.config import SigMLConfig


class Encoder(nn.Module):
    """Small CNN encoder for 28x28 grayscale images."""

    def __init__(self, channels: list[int], fc_dim: int) -> None:
        super().__init__()
        layers: list[nn.Module] = []
        in_ch = 1
        for out_ch in channels:
            layers.extend([
                nn.Conv2d(in_ch, out_ch, 3, padding=1),
                nn.BatchNorm2d(out_ch),
                nn.ReLU(inplace=True),
                nn.MaxPool2d(2),
            ])
            in_ch = out_ch
        self.conv = nn.Sequential(*layers)

        # After two 2x poolings on 28x28: 7x7
        self.fc = nn.Linear(channels[-1] * 7 * 7, fc_dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        h = self.conv(x)
        h = h.flatten(1)
        return F.relu(self.fc(h))


class SignificanceModel(nn.Module):
    """Full model with genus head + 10 differentia heads.

    Outputs:
      logit_G:  [B]      genus logit (digit vs non-digit)
      chi_G:    [B]      genus depth score
      logit_D:  [B, 10]  differentia logits (one per digit)
      chi_D:    [B, 10]  differentia depth scores
    """

    def __init__(self, config: SigMLConfig) -> None:
        super().__init__()
        self.config = config
        fc = config.encoder_fc_dim

        self.encoder = Encoder(config.encoder_channels, fc)

        # Genus head: pred + depth
        self.genus_pred = nn.Linear(fc, 1)
        self.genus_depth = nn.Linear(fc, 1)

        # Differentia heads: pred + depth (10 each)
        self.diff_pred = nn.Linear(fc, config.n_diff)
        self.diff_depth = nn.Linear(fc, config.n_diff)

    def forward(
        self, x: torch.Tensor,
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        h = self.encoder(x)

        logit_G = self.genus_pred(h).squeeze(-1)     # [B]
        chi_G = self.genus_depth(h).squeeze(-1)       # [B]
        logit_D = self.diff_pred(h)                   # [B, 10]
        chi_D = self.diff_depth(h)                    # [B, 10]

        return logit_G, chi_G, logit_D, chi_D
