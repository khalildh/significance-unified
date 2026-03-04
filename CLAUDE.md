# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A hybrid Lean 4 formalization + PyTorch ML project proving that rhetorical amplification (Kennedy) and Aristotelian essential definition (Rand) share common mathematical structure — a preorder on concepts built from two comparison primitives on an integer scale (χ : α → ℤ).

## Build & Run Commands

### Lean
```bash
lake exe cache get    # Download pre-built Mathlib binaries (do this first)
lake build            # Build and typecheck all proofs
```

### Python ML
```bash
python3 -m venv .venv && .venv/bin/pip install -e ".[dev]"  # Setup

# Supervised experiment
.venv/bin/python -m sigml.train --n-epochs 10
.venv/bin/python -m sigml.report

# Unsupervised experiment (N-level hierarchy)
.venv/bin/python -m sigml.unsup_train --n-epochs 30
.venv/bin/python -m sigml.unsup_train --n-epochs 2 --n-levels 3 --k-min 4 --k-max 32  # smoke test
.venv/bin/python -m sigml.unsup_report --model results/unsup_model.pt
```

No test suite — Lean is self-verifying via typechecking; Python uses `evaluate()` in train.py for metrics.

## Architecture

### Lean Formalization (`SignificanceUnified/`)
- **Basic.lean** (sections 1–13): Core definitions, embeddings, unification theorem
- **Consequences.lean** (sections 14–27): Derived theorems (square of opposition, syllogistic)

Two comparison primitives kept deliberately separate (different algebraic structure):
- **Raise** — strict ordering (`a < b`), transitive. Models essential definition hierarchy.
- **SimilarByContrast** — ternary gap relation, NOT transitive. Grounds concept differentiation.

Both embed into `SignificanceRaise`; round-trip theorems prove honest bijection.

### Python ML (`src/sigml/`)

**Supervised** (`model.py`, `losses.py`, `train.py`, `data.py`, `report.py`):
CNN encoder → genus head (digit vs non-digit) + 10 differentia heads (which digit). Five losses map directly to Lean definitions: genus BCE, differentia CE, raise hinge, contrast triplet, one-hot exclusivity.

**Unsupervised** (`unsup_*.py`):
N-level hierarchical model with overcomplete initialization + CCD₃ witnessability pruning. Both width (prototypes per level) and depth (number of alive levels) are discovered automatically. No labels used — PrototypeLayer with temperature-scaled cosine similarity discovers clusters. Post-hoc purity evaluation.

Dataset: MNIST digits + Fashion-MNIST non-digits (120k images total).

## Key Conventions

- **"Koncept"** not "concept" — avoids Lean keyword collision
- Every Python loss/model component has a docstring noting its Lean counterpart ("Maps to: ...")
- Config dataclass (`SigMLConfig` in `config.py`) holds all hyperparameters
- Losses return `(scalar, details_dict)` tuple for logging
- Device auto-detection: CUDA > MPS > CPU (MPS fallback enabled in `__init__.py`)
- Deterministic seeding (default seed=42) throughout
- Integer scale (ℤ not ℝ) chosen for decidability in Lean proofs

## Git Branches
- **main**: Lean formalization only
- **ml-mnist**: Adds supervised + unsupervised ML experiments
