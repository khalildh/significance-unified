# Significance as a Preorder: From Formal Proof to Learned Representation

## Motivation

The Lean formalization on the `main` branch proves that rhetorical amplification (Kennedy) and Aristotelian essential definition (Rand) share a common mathematical structure: a preorder on concepts built from two distinct comparison primitives on a single integer scale.

This branch asks: **can a neural network learn that structure from data?**

Specifically, we train a model on MNIST (handwritten digits) and Fashion-MNIST (clothing items) to learn the formal objects defined in `Basic.lean` — genus, differentia, the Raise relation, and SimilarByContrast witnesses — entirely from images.

## The formal structure (recap)

The Lean formalization defines five key objects:

| Lean object | What it means |
|---|---|
| `Koncept.pred` | Which entities belong to the concept |
| `Koncept.χ` | A depth score on a single integer scale |
| `KonceptDef.isEssential` | `Raise(genus.χ a)(differentia.χ a)` — differentia is strictly deeper than genus on every member |
| `CCDWitness₃` | Two members and a contrast outsider satisfying `SimilarByContrast` |
| `definiendum = genus.meet differentia` | The defined concept is exactly the intersection of genus and differentia |

The key philosophical claim is that these are **two different kinds of comparison** on the same scale:

- **Raise** (level comparison): directional, transitive, composes into chains
- **SimilarByContrast** (gap comparison): symmetric in the similar pair, not transitive, does not compose

Conflating them is a category mistake. A neural network that learns both separately would be evidence that the distinction is not just formal but empirically grounded.

## The experiment

### Domain

- **Genus**: "handwritten digit" — learned by contrasting MNIST images (digits) against Fashion-MNIST images (clothing). The genus is nontrivial because the model must learn to distinguish these two visual domains.
- **Differentiae**: 10 learned axes, one per digit class (0–9). Each differentia separates its digit from all others.
- **Definiendum**: digit *i* = genus ∧ differentia *i* (the meet).

This gives us 10 essential definitions sharing a single genus — 10 species under one genus, exactly as Aristotle describes.

### Architecture

A small CNN encoder (two conv blocks, batch norm, max pooling) produces a shared representation. Four linear heads read from it:

| Head | Output | Lean analogue |
|---|---|---|
| `genus_pred` | logit for "is a digit?" | `genus.pred` |
| `genus_depth` | scalar χ_G | `genus.χ` |
| `diff_pred` | 10 logits, one per digit | `differentia_i.pred` |
| `diff_depth` | 10 scalars χ_D | `differentia_i.χ` |

### Training objective

Five losses, each corresponding to a piece of the formalization:

**1. Genus loss** (`L_genus`) — Binary cross-entropy for digit vs. non-digit.
Maps to: learning `genus.pred`.

**2. Differentia loss** (`L_diff`) — Cross-entropy over the 10 differentia heads, applied only on digit images.
Maps to: learning `differentia_i.pred`.

**3. Raise loss** (`L_raise`) — Hinge loss enforcing χ_G(x) + margin < χ_D_i(x) on images of digit *i*.
Maps to: `isEssential : ∀ a, definiendum.pred a → Raise (genus.χ a) (differentia.χ a)`.

This is the directed, explanatory ordering. The loss does not follow from the contrast loss — it is additional structure, exactly as in the Lean formalization where `isEssential` is a separate field from `ccd`.

**4. Contrast loss** (`L_contrast`) — Triplet loss on the differentia depth axes. For each digit *i*, we mine triplets (a, b, c) where a and b are digit *i* and c is a different digit:

```
max(0, margin + |χ_Di(a) - χ_Di(b)| - |χ_Di(a) - χ_Di(c)|)
+ max(0, margin + |χ_Di(a) - χ_Di(b)| - |χ_Di(b) - χ_Di(c)|)
```

This is a soft version of the two gap inequalities in `SimilarByContrast`:

```lean
def SimilarByContrast (a b c : Depth) : Prop :=
  a ≠ b ∧ Gap a b < Gap a c ∧ Gap a b < Gap b c
```

Each satisfied triplet is an empirical CCDWitness₃.

**5. Exclusivity loss** (`L_onehot`) — Penalizes having more than one differentia active per digit image: `(Σ_i sigmoid(logit_Di) - 1)²`.
Maps to: differentiae are mutually exclusive (each digit has exactly one).

### What the raise loss buys you (that contrast alone doesn't)

The contrast loss grounds *similarity* — it learns that two 3s are closer to each other than to a 7 on the "3-ness" axis. But it does not determine *direction*. It cannot tell you which concept is genus and which is differentia.

The raise loss adds directed ordering: differentia is strictly above genus in depth. This mirrors the Lean proof that `SimilarByContrast.hasRaise` gives `Raise a b ∨ Raise b a` (some direction exists) but not which one. The `isEssential` field supplies the specific direction.

Training both losses together is the empirical version of the formal claim: **contrast grounds grouping; raise encodes explanatory priority; they are not the same structure.**

## Results (10 epochs, MPS)

### Classification

| Metric | Value |
|---|---|
| Genus accuracy (digit vs non-digit) | 99.99% |
| Digit accuracy (argmax differentia) | 99.11% |
| Meet accuracy (pG × pDi) | 99.11% |

The meet accuracy matching the digit accuracy means the model treats `definiendum ≈ genus ∧ differentia` — the genus head is not interfering with digit classification, it is complementing it. This is the empirical analogue of `definiendum = genus.meet differentia`.

### Raise satisfaction

| Metric | Value |
|---|---|
| Raise rate (χ_G < χ_D[true]) | 100.00% |
| Mean χ_G on digits | −25.77 |
| Mean χ_D[true digit] | +2.58 |
| Mean gap (D − G) | 28.35 |

On every single test digit image, the differentia depth score is strictly above the genus depth score. The mean gap of 28.35 far exceeds the training margin of 1.0. The model has learned a strong, consistent directional ordering between genus and differentia.

### CCD witnesses

For each digit, the report extracts triplets (anchor, positive, contrast) and checks the `SimilarByContrast` gap inequalities:

| Digit | Contrast digit | |a−b| | |a−c| | |b−c| | Holds? |
|---|---|---|---|---|---|
| 0 | 3 | 0.000 | 39.789 | 39.788 | ✓ |
| 1 | 7 | 0.001 | 32.028 | 32.029 | ✓ |
| 2 | 3 | 0.002 | 36.107 | 36.105 | ✓ |
| 3 | 7 | 0.002 | 55.373 | 55.375 | ✓ |
| 4 | 3 | 0.000 | 28.006 | 28.006 | ✓ |
| 5 | 3 | 0.001 | 40.576 | 40.575 | ✓ |
| 6 | 7 | 0.001 | 27.807 | 27.808 | ✓ |
| 7 | 3 | 0.005 | 49.417 | 49.412 | ✓ |
| 8 | 7 | 0.000 | 37.941 | 37.941 | ✓ |
| 9 | 7 | 0.002 | 44.807 | 44.809 | ✓ |

Every witness satisfies both gap inequalities of `SimilarByContrast`. The within-class gaps (|a−b|) are near zero while the between-class gaps (|a−c|, |b−c|) are large, meaning the model clusters same-digit images very tightly on each differentia axis.

All contrast entities are different digits that share the genus (they are still digits) but lack the target differentia — matching the Lean field `ccd_contrast : ¬differentia.pred contrast`.

## What this demonstrates

1. **The formal structure is learnable.** A standard CNN with appropriate loss functions recovers all five components of an essential definition from pixel data.

2. **The two comparisons are empirically distinct.** The contrast loss and the raise loss train different heads and produce different artifacts (triplets vs. directed depth gaps). Removing either one would lose information the other cannot recover.

3. **The "meet" decomposition works.** Digit classification accuracy is identical whether you use the differentia head alone or the genus × differentia product. The genus adds real information (digit vs. non-digit) without degrading the differentia signal.

4. **Contrast witnesses are concrete and visual.** Each CCD witness is a triple of actual images you can inspect. This is the interpretability payoff: not just "the model classified this correctly" but "here are two 3s that are similar, contrasted with this 7, and the model can show you why on a specific axis."

## Running the experiment

```bash
git checkout ml-mnist
python3 -m venv .venv
.venv/bin/pip install -e ".[dev]"

# Train (10 epochs, ~2 minutes on MPS)
.venv/bin/python -m sigml.train --n-epochs 10

# Generate interpretability report
.venv/bin/python -m sigml.report
```

## File structure

```
src/sigml/
  config.py    — Hyperparameters (SigMLConfig dataclass)
  data.py      — MNIST + Fashion-MNIST combined dataset
  model.py     — CNN encoder + genus/differentia heads
  losses.py    — Five losses mapping to the Lean formalization
  train.py     — Training loop with evaluation
  report.py    — Interpretability report generator
```
