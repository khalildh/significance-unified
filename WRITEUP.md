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

---

## Part II: Unsupervised Discovery

The supervised experiment above shows the formal structure is learnable when labels are provided. But the stronger test is: **can the structure emerge without any labels at all?**

If genus and differentia are real structure in the data — not just artifacts of our labeling scheme — then a model trained with only the formal constraints (raise, contrast, hierarchy) should discover *some* genus/differentia decomposition, even if it doesn't match the human one.

### Setup

The unsupervised model sees the same 120,000 images (60k MNIST + 60k Fashion-MNIST) but receives **no labels during training**. Eval labels (0–19) are retained only for post-hoc interpretation of what the model discovered.

#### Architecture

Same CNN encoder as the supervised version, but the classification heads are replaced with **prototype layers** — learned centroids in embedding space. Cluster assignment is soft nearest-neighbour with temperature-scaled cosine similarity:

```
image → CNN encoder → z ∈ ℝ^128
                      ↓
         ┌────────────┴────────────┐
    Genus head               Differentia head
  z_G ∈ ℝ^64              z_D ∈ ℝ^64
  χ_G ∈ ℝ  (depth)        χ_D ∈ ℝ  (depth)
  p_G ∈ Δ^4  (soft)       p_D ∈ Δ^20 (soft)
```

The model must discover up to 4 genus clusters and up to 20 differentia clusters from the raw pixel data.

| Model output | Lean analogue |
|---|---|
| `p_G` (soft assignment to 4 genus prototypes) | `genus.pred` |
| `χ_G` (genus depth scalar) | `genus.χ` |
| `p_D` (soft assignment to 20 diff prototypes) | `differentia.pred` |
| `χ_D` (differentia depth scalar) | `differentia.χ` |

#### Five unsupervised losses

Each loss is derived from the Lean formalization, but uses the model's own cluster assignments as pseudo-labels:

**1. Genus contrast** (`L_gc`) — Triplet loss on genus embeddings. Images assigned to the same genus cluster should be closer than images from different genus clusters. Maps to: `SimilarByContrast` at the genus level (CCD₃ witnesses for genus).

**2. Differentia contrast** (`L_dc`) — Triplet loss on differentia embeddings. Same structure as genus contrast but at the finer differentia level. Maps to: `SimilarByContrast` at the differentia level.

**3. Raise** (`L_raise`) — Hinge loss enforcing χ_G < χ_D on every image. Identical to the supervised version — this is the directed depth ordering. Maps to: `KonceptDef.isEssential`.

**4. Hierarchy** (`L_hier`) — Minimizes the conditional entropy H(p_G | p_D). Knowing which differentia cluster an image belongs to should determine its genus cluster. Maps to: `definiendum = genus.meet differentia`.

**5. Uniformity** (`L_uniform`) — Maximizes the entropy of the marginal cluster distributions, preventing any single cluster from absorbing all images. Maps to: `no_universal_ccd` — the Lean proof that a universal concept cannot be CCD-grounded.

The key design principle: **the losses encode formal constraints, not semantic content.** The model is told "there should be two levels of clustering, the deeper one should be finer, and both should have contrast witnesses" — but never told what those clusters should contain.

### Results (30 epochs, MPS)

#### Formal properties — all satisfied

| Property | Result | Lean analogue |
|---|---|---|
| Raise satisfaction | **100.00%** | `isEssential` |
| Mean χ_G | −1.48 | genus depth |
| Mean χ_D | +1.12 | differentia depth |
| Mean gap (χ_D − χ_G) | 2.60 | raise margin |
| CCD witnesses verified | **15/15** | `CCDWitness₃` |
| Genus clusters active | 4/4 | no collapse |
| Diff clusters active | 18/20 | meaningful partition |
| Hierarchy (diff → genus) | 49–100% | `genus.meet differentia` |

The formal structure is fully present: raise is universally satisfied, every tested cluster has valid contrast witnesses, and the hierarchy from differentia to genus is largely clean.

#### What the model discovered

The model did NOT learn the human digit/fashion distinction as its genus. Instead, it discovered a **visual shape geometry**:

**Genus clusters (shape families):**

| Cluster | Size | Top categories | Interpretation |
|---|---|---|---|
| 0 | 6,706 | Coat, Pullover, Shirt | **Broad torso silhouettes** |
| 1 | 5,363 | digit-7, digit-9, digit-4 | **Thin angular strokes** |
| 2 | 5,753 | digit-1, Sneaker, digit-6 | **Narrow/elongated shapes** |
| 3 | 2,178 | digit-0, Bag | **Closed round shapes** |

The model groups a sneaker with the digit 1 (both elongated), a bag with the digit 0 (both round), and coats with pullovers (both broad). It found a genuine visual principle — just not the one humans would choose.

**Notable differentia clusters:**

| Cluster | Size | Purity | Top category | What it captured |
|---|---|---|---|---|
| 14 | 772 | 72% | digit-1 (553) | Vertical stroke |
| 1 | 95 | 73% | digit-7 (69) | Angled stroke with crossbar |
| 7 | 232 | 73% | digit-7 (169) | Same — the model split digit-7 across two clusters |
| 10 | 14 | 100% | Trouser (14) | Two-legged silhouette (small but pure) |
| 16 | 1,007 | 50% | digit-0 (500) | Round enclosed shapes |
| 8 | 2,636 | 33% | T-shirt (872) | Upper garments |
| 15 | 3,047 | 31% | Sneaker (936) | Low-profile horizontal shapes |
| 4 | 3,191 | 29% | digit-2 (930), digit-6 (922) | Curvy digits with similar strokes |

#### CCD witnesses

All 15 tested cluster witnesses satisfy both gap inequalities of `SimilarByContrast`:

| Cluster label | Contrast label | \|a−b\| | \|a−c\| | \|b−c\| | Holds? |
|---|---|---|---|---|---|
| digit-0 | digit-2 | 0.011 | 1.891 | 1.880 | Yes |
| digit-7 | digit-2 | 0.032 | 1.532 | 1.564 | Yes |
| digit-2 | fashion-Sandal | 0.538 | 2.079 | 1.541 | Yes |
| digit-1 | digit-2 | 0.107 | 1.548 | 1.655 | Yes |
| fashion-Trouser | digit-2 | 0.067 | 1.769 | 1.701 | Yes |
| digit-0 | fashion-Sandal | 0.106 | 1.362 | 1.468 | Yes |

Within-cluster gaps (|a−b|) are consistently an order of magnitude smaller than cross-cluster gaps — the model has learned tight, contrastively grounded clusters.

### Interpretation

#### What works

The unsupervised model satisfies **every formal axiom** in the Lean formalization:

1. **Raise** is universal — χ_D > χ_G on every image, with no label telling the model which level is "deeper."
2. **CCD witnesses** exist for every active cluster — each cluster is contrastively grounded in the sense of `SimilarByContrast`.
3. **Hierarchy** holds — differentia clusters map predominantly to single genus clusters, approximating `definiendum = genus ∧ differentia`.
4. **No universal cluster** — the uniformity loss prevents collapse, matching the `no_universal_ccd` theorem.

#### What's philosophically interesting

The model found a **different ontology** from the human one while satisfying the same formal axioms. Humans would put all digits in one genus and all clothing in another. The neural network instead organized by visual geometry: round things together, angular things together, elongated things together.

This demonstrates something the Lean formalization was designed to capture: **the formal structure of concept formation is independent of the specific concepts formed.** The axioms constrain the *shape* of a conceptual system (two levels, directed depth ordering, contrastive grounding, hierarchical meet) without dictating its *content*. Different agents — human, neural network, or any other — can satisfy the same axioms with genuinely different genus/differentia decompositions.

The digit-1 cluster (72% pure, 553 images) and the digit-7 clusters (73% pure) show the model *is* finding some human-recognizable structure. But it finds it through visual similarity, not semantic knowledge. Two 7s look alike; a 7 and a 4 share angular geometry. The model's "genus" for them is "angular stroke" — a perfectly valid genus by the formal criteria, just not the one we'd choose.

#### Comparison: supervised vs unsupervised

| | Supervised | Unsupervised |
|---|---|---|
| Labels used in training | Yes | No |
| Genus accuracy | 99.99% | N/A (no "correct" answer) |
| Diff purity | 99.11% | 26% (best 34%) |
| Raise satisfaction | 100% | 100% |
| CCD witnesses valid | 10/10 | 15/15 |
| What genus captures | digit vs fashion | visual shape family |
| Formal axioms satisfied | All | All |

The formal structure is satisfied in both cases. The difference is in cluster *quality* relative to human labels — which is expected, since the unsupervised model was never told what clusters to find. The supervised model learns *our* ontology; the unsupervised model discovers *its own*.

## Running the experiments

```bash
git checkout ml-mnist
python3 -m venv .venv
.venv/bin/pip install -e ".[dev]"

# Supervised (10 epochs, ~2 min on MPS)
.venv/bin/python -m sigml.train --n-epochs 10
.venv/bin/python -m sigml.report

# Unsupervised (30 epochs, ~10 min on MPS)
.venv/bin/python -m sigml.unsup_train
.venv/bin/python -m sigml.unsup_report --model results/unsup_model.pt
```

## File structure

```
src/sigml/
  # Supervised
  config.py        — Hyperparameters (SigMLConfig dataclass)
  data.py          — MNIST + Fashion-MNIST combined dataset (with labels)
  model.py         — CNN encoder + genus/differentia heads
  losses.py        — Five supervised losses
  train.py         — Training loop with evaluation
  report.py        — Interpretability report generator

  # Unsupervised
  unsup_model.py   — CNN encoder + prototype layers (no classification heads)
  unsup_data.py    — MNIST + Fashion-MNIST as unlabeled stream
  unsup_losses.py  — Five unsupervised losses (contrast, raise, hierarchy, uniformity)
  unsup_train.py   — Training loop with post-hoc cluster evaluation
  unsup_report.py  — Interpretability report (CCD witnesses, hierarchy check)
```
