"""
data.py — Mixed unlabeled dataset for unsupervised significance learning.

Combines MNIST and Fashion-MNIST into a single stream with NO domain labels
and NO class labels. The model must discover genus/differentia structure
entirely from the contrastive and depth-ordering losses.

The only label retained is an integer 0-19:
  0-9:  MNIST digits (used ONLY for evaluation, never for training)
  10-19: Fashion-MNIST items (used ONLY for evaluation)

During training, these labels are ignored. They are returned so the
evaluation loop can measure whether the discovered clusters align with
the ground truth without the training loop ever seeing them.
"""

from dataclasses import dataclass

import torch
from torch.utils.data import Dataset, DataLoader
from torchvision import datasets, transforms


@dataclass
class DataConfig:
    batch_size: int = 256
    num_workers: int = 0
    data_root: str = "./data"
    # How many images to use per dataset (None = all)
    mnist_limit: int | None = None
    fashion_limit: int | None = None


class UnlabeledMixed(Dataset):
    """
    Wraps MNIST + Fashion-MNIST as a single unlabeled stream.

    Returns (image, eval_label) where eval_label is:
      0-9  for MNIST digits
      10-19 for Fashion-MNIST items

    The eval_label is ONLY for post-hoc cluster evaluation.
    The training losses in losses.py never receive it.
    """

    def __init__(self, mnist_split: str, fashion_split: str, root: str,
                 mnist_limit=None, fashion_limit=None):
        assert mnist_split in ("train", "test")
        transform = transforms.Compose([
            transforms.ToTensor(),
            transforms.Normalize((0.5,), (0.5,)),
        ])
        train_flag = (mnist_split == "train")

        mnist = datasets.MNIST(root, train=train_flag,
                               download=True, transform=transform)
        fashion = datasets.FashionMNIST(root, train=train_flag,
                                        download=True, transform=transform)

        if mnist_limit is not None:
            mnist = torch.utils.data.Subset(mnist, range(mnist_limit))
        if fashion_limit is not None:
            fashion = torch.utils.data.Subset(fashion, range(fashion_limit))

        self.mnist = mnist
        self.fashion = fashion
        self.mnist_len = len(mnist)
        self.fashion_len = len(fashion)

    def __len__(self):
        return self.mnist_len + self.fashion_len

    def __getitem__(self, idx):
        if idx < self.mnist_len:
            img, label = self.mnist[idx]
            eval_label = label  # 0-9
        else:
            img, label = self.fashion[idx - self.mnist_len]
            eval_label = label + 10  # 10-19
        return img, eval_label


def make_loaders(cfg: DataConfig):
    """
    Returns (train_loader, test_loader).

    Both yield (images, eval_labels) batches.
    Training code should use only images; eval code may use eval_labels.
    """
    train_ds = UnlabeledMixed(
        "train", "train", cfg.data_root,
        cfg.mnist_limit, cfg.fashion_limit
    )
    test_ds = UnlabeledMixed(
        "test", "test", cfg.data_root,
        cfg.mnist_limit, cfg.fashion_limit
    )

    train_loader = DataLoader(
        train_ds,
        batch_size=cfg.batch_size,
        shuffle=True,
        num_workers=cfg.num_workers,
        pin_memory=True,
        drop_last=True,
    )
    test_loader = DataLoader(
        test_ds,
        batch_size=cfg.batch_size,
        shuffle=False,
        num_workers=cfg.num_workers,
        pin_memory=True,
    )
    return train_loader, test_loader
