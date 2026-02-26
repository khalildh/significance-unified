# Significance as a Preorder — A Unified Formalization

A Lean 4 formalization (with Mathlib) that models **significance as a preorder**, unifying two traditions that both rely on the same underlying operation — comparing things on a scale — but that have never been formally connected:

- **Rhetorical amplification** (Kennedy's reading of classical rhetoric): a speaker raises the significance of a subject by comparing it to a baseline on a scale of depth
- **Aristotelian essential definition** (Rand's Objectivist epistemology): a concept's differentia is more explanatorily significant than its genus — rationality is "deeper" than animality in defining Man

Both traditions perform the same move: *asserting that one thing is strictly greater than another on a shared scale*. This formalization makes that shared structure explicit and machine-checkable.

## The key insight: one scale, two comparisons

Everything starts from a single integer scale — a **characteristic** `χ : α → ℤ` that assigns a "depth" to each entity. But concept-formation requires **two** kinds of comparison on that scale, not one:

### Level comparison (Raise)

```
Raise a b  iff  a < b
```

A strict order on depth values. Used when you need to say "this is more significant than that" — differentia over genus, sacrilege over theft, the sacred over the profane. Level comparisons compose transitively: if A < B and B < C, then A < C. This is what makes Cicero's chains of amplification work, and what makes "genus → differentia" a directed claim.

### Gap comparison (SimilarByContrast)

```
SimilarByContrast a b c  iff  a ≠ b ∧ |a - b| < |a - c| ∧ |a - b| < |b - c|
```

A ternary relation: *a and b are similar as contrasted with c*. Used when you need to say "these two belong together compared to that outsider" — dogs and wolves are similar compared to cats. Gap comparisons are **relative** and do **not** compose transitively. The fact that dogs and wolves are similar relative to cats, and wolves and foxes are similar relative to elephants, does not chain into a single comparison.

### Why the separation matters

Forcing both into a single binary relation would conflate them. You'd either lose the transitivity that makes level comparisons useful for chains of argument, or you'd falsely attribute transitivity to gap comparisons that don't have it. The formalization keeps them separate so each carries exactly the structure it actually has.

From the `a ≠ b` conjunct of `SimilarByContrast`, a `Raise` in *some* direction follows (by linearity of ℤ) — but the gap inequalities themselves don't determine which direction. Contrast tells you things differ; only level comparison tells you which is deeper.

## How concepts work

A **Koncept** pairs a predicate (which entities fall under the concept) with a characteristic (how deep each entity is on that concept's scale):

```lean
structure Koncept (α : Type) where
  pred : α → Prop          -- which entities are units of this concept
  χ    : Characteristic α   -- degree of possession of the characteristic
```

Concepts form a **preorder by extension**: concept A ≤ concept B when every unit of A is also a unit of B. This is deliberately extensional — it says nothing about the characteristic scales. "All men are animals" is a statement about which things fall under each concept, not about depths.

### Contrast-grounded differentiation (CCD₃)

A well-formed concept isn't just a predicate with a scale — it's **grounded** in contrast. The CCD₃ axiom says: for any two distinct units of a concept, there exists something *outside* the concept such that the two units are closer to each other (in χ) than either is to the outsider.

This is what makes a concept a concept rather than an arbitrary grouping. Dogs and wolves belong together *as contrasted with* cats. Man and human belong together *as contrasted with* dog. The outsider is what gives the grouping its identity.

`CCDWitness₃` records a specific contrast witness as evidence, rather than asserting global existence. This is better for proof engineering — you carry the evidence through your proofs rather than appealing to a blanket axiom.

### Essential definitions (KonceptDef)

An essential definition has three parts: **definiendum** (the concept being defined), **genus** (the broader category), and **differentia** (what distinguishes it). The definiendum is the meet of genus and differentia — you're in the defined concept exactly when you're in both the genus and the differentia.

The critical constraint: for every unit of the definiendum, the differentia is strictly deeper than the genus — `Raise (genus.χ a) (differentia.χ a)`. Rationality (depth 3) is deeper than animality (depth 1) for every man. This is what makes the definition *essential* rather than accidental.

A CCD witness grounds **why** the raise is essential. Without it, `isEssential` could be satisfied by any arbitrary scale assignment. The witness shows that the units of the concept actually cluster together relative to things that lack the differentia.

## How amplification works

Kennedy's analysis of classical rhetoric identifies amplification as the master move: *raise the significance of a subject above a baseline*. An `AmplificationMove` carries:

- A **comparison** (baseline ≤ subject on the depth scale)
- A **canon** (invention, style, or arrangement — which rhetorical art is being employed)
- A **dimension** (vertical or horizontal — raising vs. expanding)
- A **mode** (logical, pathetic, ethical, or spiritual — how the audience is moved)
- A proof that the comparison is **strict** (a genuine `Raise`, not mere equality)

Amplification moves compose when they share an endpoint and match on canon, dimension, and mode — this is Cicero's technique of chaining comparisons: theft < sacrilege < treason, each step raising the significance further.

## The unification

Both traditions produce the same abstract object — a `SignificanceRaise`:

```lean
structure SignificanceRaise where
  baseline : Depth
  subject  : Depth
  isStrict : Raise baseline subject
```

Two total embeddings connect the traditions to this shared structure:

1. **AmplificationMove → SignificanceRaise**: forget the rhetorical metadata (canon, dimension, mode), keep the strict comparison
2. **KonceptDef → SignificanceRaise**: for a given unit of the definiendum, the genus depth is the baseline and the differentia depth is the subject

The `AmplificationOver` structure makes the connection bidirectional. It combines a concept definition with an amplification move and proves they agree on baseline and subject. The round-trip theorems show this is an honest bijection on the concept fields — nothing is lost or fabricated in translation.

The **unified significance theorem** then states: when an amplification move is grounded in a concept definition, the rhetorical raise and the definitional raise have the same baseline and the same subject. They are the same comparison, viewed from two different traditions.

## From definitions to syllogisms

Every essential definition automatically licenses classical syllogistic inferences. The formalization proves this structurally:

- **Barbara** (All M are P; All S are M; therefore All S are P): `definiendum ≤ genus` and `definiendum ≤ differentia` are both instances of Barbara. "All men are animals" and "all men are rational" follow from the definition of Man — they are not additional axioms.
- **Celarent** (No M are P; All S are M; therefore No S are P): "No rational beings are dogs" follows from the concept structure.
- **Darii** (All M are P; Some S are M; therefore Some S are P): The CCD witness provides the existential — it guarantees at least two distinct units exist, so "some men exist" is a theorem, not an assumption.

The connection is direct: a good definition *is* a package of valid syllogisms. The definition of Man doesn't just classify — it licenses inference.

## Concrete examples

### Dogs, wolves, and cats (gap comparison)

```
canine χ:  dog = 5,  wolf = 6,  cat = 2

Gap(dog, wolf)  = |5 - 6| = 1
Gap(dog, cat)   = |5 - 2| = 3
Gap(wolf, cat)  = |6 - 2| = 4

1 < 3  ✓  (dog and wolf closer than dog and cat)
1 < 4  ✓  (dog and wolf closer than wolf and cat)
```

Dogs and wolves are similar as contrasted with cats. The `hasRaise` theorem then tells us: since dog ≠ wolf on the scale, there's a raise in one direction — but it's the contrast that groups them, not the direction.

### Man = Rational Animal (level comparison)

```
konceptAnimal.χ:    man = 1, human = 1, dog = 1, oak = 0
konceptRational.χ:  man = 3, human = 4, dog = 0, oak = 0

For man:   Raise 1 3  ✓  (rationality deeper than animality)
For human: Raise 1 4  ✓
```

The CCD witness: man and human are similar as rational animals, contrasted with dog (who lacks rationality). Gap(3,4) = 1 < Gap(3,1) = 2 < Gap(4,1) = 3.

### Cicero's chain (transitive composition)

```
cicero1: Raise 2 5    (first step)
cicero2: Raise 5 9    (second step)
chain:   Raise 2 9    (composed — transitivity of <)
```

Level comparisons chain. This is Cicero's technique: build significance step by step, and the total raise is guaranteed by transitivity.

## File structure

| Section | Lines | Content |
|---------|-------|---------|
| 1 | 46–121 | `Raise`, `Gap`, `SimilarByContrast` — the two comparison primitives |
| 2 | 140–200 | `Koncept`, `CCD₃`, `CCDWitness₃`, preorder instance, meet/join |
| 3 | 230–256 | `KonceptDef` — essential definitions with CCD grounding |
| 4 | 263–333 | `AmplificationMove` — Kennedy's rhetorical moves |
| 5 | 340–368 | `SignificanceRaise` — the shared abstract structure |
| 6 | 357–368 | Two total embeddings into `SignificanceRaise` |
| 7 | 374–449 | `AmplificationOver`, round-trip proofs, unified significance theorem |
| 8 | 459–474 | Example: dogs, wolves, cats (gap comparison) |
| 9 | 483–558 | Example: Man = Rational Animal (level comparison) |
| 10 | 565–583 | Cicero's argument chain (transitive composition) |
| 11 | 610–648 | Classical syllogisms: Barbara, Celarent, Darii |
| 12 | 660–683 | Syllogisms derived from essential definitions |
| 13 | 690–723 | Concrete syllogisms: all men are animals, etc. |

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
curl https://elan-init.lean-lang.org/ -sSf | sh
lake exe cache get   # downloads pre-built Mathlib oleans
lake build
```

## Design decisions

- **ℤ not ℝ for depth**: Integer scales are decidable, which lets `native_decide` handle concrete examples automatically. The theory doesn't need density or completeness.
- **Preorder by extension only**: The concept ordering `c ≤ d` means every unit of `c` is a unit of `d`. It deliberately does not constrain `χ`. If you need "concept refinement preserves the characteristic," you'd strengthen the order.
- **CCDWitness₃ over CCD₃**: Carrying a specific witness is better for proof engineering than asserting global existence. You know exactly which entities ground the concept.
- **`noncomputable` for Classical uses**: Meet/join use `Classical` (for `max` on arbitrary types). Concrete examples like `konceptMan` are defined computably so `native_decide` works in proofs.
- **Separate `Koncept` spelling**: Avoids collision with Lean's `concept` keyword while being visually distinct.
