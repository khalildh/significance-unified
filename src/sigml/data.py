"""Data loading: MNIST (digits) + Fashion-MNIST (non-digits)."""

from __future__ import annotations

import os

import torch
from torch.utils.data import Dataset, DataLoader
from torchvision import datasets, transforms


class DigitNonDigitDataset(Dataset):
    """Combined dataset: MNIST digits (genus=1) + Fashion-MNIST (genus=0).

    Each item returns (image, y_genus, y_digit) where:
      - image: [1, 28, 28] float tensor
      - y_genus: 1.0 if digit, 0.0 if non-digit
      - y_digit: 0-9 if digit, -1 if non-digit
    """

    def __init__(self, train: bool = True, data_dir: str = "data") -> None:
        transform = transforms.Compose([
            transforms.ToTensor(),
            transforms.Normalize((0.5,), (0.5,)),
        ])

        self.mnist = datasets.MNIST(
            root=data_dir, train=train, download=True, transform=transform,
        )
        self.fashion = datasets.FashionMNIST(
            root=data_dir, train=train, download=True, transform=transform,
        )

    def __len__(self) -> int:
        return len(self.mnist) + len(self.fashion)

    def __getitem__(self, idx: int) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        if idx < len(self.mnist):
            img, label = self.mnist[idx]
            return img, torch.tensor(1.0, dtype=torch.float32), torch.tensor(label, dtype=torch.long)
        else:
            img, _ = self.fashion[idx - len(self.mnist)]
            return img, torch.tensor(0.0, dtype=torch.float32), torch.tensor(-1, dtype=torch.long)


def make_dataloaders(
    config,
    num_workers: int = 0,
) -> tuple[DataLoader, DataLoader]:
    """Create train and test DataLoaders."""
    train_ds = DigitNonDigitDataset(train=True)
    test_ds = DigitNonDigitDataset(train=False)

    g = torch.Generator().manual_seed(config.seed)

    train_loader = DataLoader(
        train_ds,
        batch_size=config.batch_size,
        shuffle=True,
        generator=g,
        num_workers=num_workers,
        drop_last=True,
    )
    test_loader = DataLoader(
        test_ds,
        batch_size=config.batch_size,
        shuffle=False,
        num_workers=num_workers,
    )
    return train_loader, test_loader
