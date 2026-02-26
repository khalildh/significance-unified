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

## Surprising consequences

The formalization derives several results that are **stated as rules or principles** in the philosophical literature but have never been **proved as theorems** from a common foundation. These are in `Consequences.lean`.

### Circular definitions are mathematically impossible

`no_definition_cycle` — If essential definitions chain through their genus/differentia links (A's differentia is B's genus, B's differentia is C's genus, C's differentia loops back to A's genus), Lean proves `False`. The depth ordering would require `a < b < c < a` on ℤ, which is a contradiction.

Aristotle prohibits circular definitions in the *Posterior Analytics* (I.3). Every logic textbook repeats this as a rule. Formal ontology literature describes genus-differentia hierarchies as directed acyclic graphs and treats acyclicity as a design constraint to be *imposed*.

The formalization shows it is not a constraint you impose — it is a **consequence** you get for free. Once each definition carries a strict depth comparison (`genus.χ < differentia.χ`), circularity is impossible. The integers don't have cycles in their ordering. Aristotle's prohibition is not a methodological preference but a mathematical necessity.

### "Everything" is not a concept

`no_universal_ccd` — A concept whose predicate includes every entity of the type cannot satisfy CCD₃. There is nothing outside it to serve as a contrast witness.

Aristotle says "being is not a genus." Rand treats "existence" as axiomatic, not formed by differentiation. These are presented as philosophical claims requiring argument. The formalization shows the impossibility is structural: if concepts require contrast-grounded differentiation, and a universal concept has no outsider, then it cannot be a concept. The debate is settled by the definition.

### Concept-formation requires at least two instances

`KonceptDef.has_two_units` — Every essential definition has at least two distinct units in the definiendum. Singleton concepts cannot be essentially defined.

Rand states that abstraction requires "two or more concretes." She presents this as an epistemological observation about how the mind forms concepts. The formalization shows it is a logical necessity: the CCD witness must exhibit two distinct entities inside the concept. The type system will not let you construct a `KonceptDef` with fewer. What Rand stated as a claim about cognition is a constraint on the mathematical structure itself.

### Definition chains compose

`KonceptDef.chain` — If the differentia of one definition serves as the genus of a refinement (e.g., Man = Rational Animal, Philosopher = Contemplative Rational), then for any entity that is a unit of both, the total depth gain composes: contemplation > animality.

This is not obvious because the two definitions use different characteristic functions. The theorem shows they compose **only when** the linking condition holds (`d2.genus = d1.differentia`), which forces the scales to agree at the junction. Without that identity, the definitions are incommensurable, and the type checker rejects the chain.

### Genus and differentia never tie

`KonceptDef.genus_lt_differentia` — In any essential definition, the genus and differentia have strictly different depths on every unit. A definition where they are equal on even one entity would mean the differentia adds nothing — it would be ornamental rather than explanatory.

### Amplification is irreversible

`AmplificationMove.irreversible` — If a rhetorical move raises the subject above the baseline, the reverse comparison cannot hold on the same scale. The asymmetry is structural: the integers do not allow `a < b` and `b < a` simultaneously.

### Concept theory requires at least three things

`CCDWitness₃.three_distinct` and `KonceptDef.min_three_entities` — The CCD witness exhibits three pairwise-distinct entities (two inside the concept, one outside). Any essential definition therefore requires a universe with at least three things. With fewer, the entire framework of contrast-grounded concepts is vacuous.

### Contrast is undirected; raise is directed

`contrast_symmetric_raise_directed` — SimilarByContrast is symmetric in its first two arguments (swapping "similar" entities preserves the relation), but Raise is not (`a < b` does not imply `b < a`). This is why `KonceptDef` needs `isEssential` as a separate field: the CCD witness determines *that* a raise exists, but not its *direction*. The choice of which concept is genus and which is differentia is additional structure that contrast alone cannot provide.

### Essential definitions are not unique

`definitions_not_unique` — The same concept can have different genus/differentia decompositions. Both "Man = Rational Animal" and "Man = Rational Sentient-being" are valid essential definitions of Man. Aristotle sometimes writes as if there is one true definition per concept. The formalization shows this is not forced by the structure — multiplicity is consistent with all the axioms.

### Definition hierarchies must terminate

`chain_depth_bound` — A chain of two essential definitions accumulates at least 2 units of depth on ℤ. More generally, k definitions in a chain contribute at least k. On a finite type with bounded depth values, this means definition hierarchies must terminate — you will eventually exhaust the available depth range. This is Aristotle's claim that definition chains bottom out in primitive, undefined terms, now proved as a mathematical consequence.

### CCDWitness₃ is weaker than CCD₃

`witness_not_implies_ccd3` — A concept can have a valid CCD witness for one pair of units without satisfying the full CCD₃ axiom across all pairs. The formalization constructs an explicit counterexample: a concept where two units are close enough for a witness, but a third unit is so far away that no outsider can bridge the gap. Whether full CCD₃ should be required is a genuine philosophical question the formalization leaves open.

### The meta-point

These twelve results were previously **separate doctrines** from different authors and different centuries — Aristotle's anti-circularity, Aristotle's "being is not a genus," Rand's "two or more concretes," the implicit compositionality of definitional hierarchies, the termination of definition chains, the non-uniqueness of definitions. The formalization shows they are all consequences of one thing: **essential definitions carry a strict depth comparison grounded in contrast**. That is the unification — not just Kennedy and Rand, but the downstream implications that were never connected before.

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

```
SignificanceUnified/
├── Basic.lean          # Core formalization (sections 1–13)
└── Consequences.lean   # Derived theorems (section 14)
```

**Basic.lean** — the core formalization:

| Section | Content |
|---------|---------|
| 1 | `Raise`, `Gap`, `SimilarByContrast` — the two comparison primitives |
| 2 | `Koncept`, `CCD₃`, `CCDWitness₃`, preorder instance, meet/join |
| 3 | `KonceptDef` — essential definitions with CCD grounding |
| 4 | `AmplificationMove` — Kennedy's rhetorical moves |
| 5 | `SignificanceRaise` — the shared abstract structure |
| 6 | Two total embeddings into `SignificanceRaise` |
| 7 | `AmplificationOver`, round-trip proofs, unified significance theorem |
| 8 | Example: dogs, wolves, cats (gap comparison) |
| 9 | Example: Man = Rational Animal (level comparison) |
| 10 | Cicero's argument chain (transitive composition) |
| 11 | Classical syllogisms: Barbara, Celarent, Darii |
| 12 | Syllogisms derived from essential definitions |
| 13 | Concrete syllogisms: all men are animals, etc. |

**Consequences.lean** — surprising derived results:

| Theorem | Content |
|---------|---------|
| `no_definition_cycle` | Circular definitions are impossible (3-cycle; generalizes to any length) |
| `no_universal_ccd` | "Everything" cannot be a contrast-grounded concept |
| `has_two_units` | Essential definitions require at least two distinct units |
| `chain` | Definition hierarchies compose transitively |
| `genus_lt_differentia` | Genus and differentia never have equal depth on any unit |
| `irreversible` | Amplification cannot be reversed |
| `three_distinct` | CCD witnesses exhibit three pairwise-distinct entities |
| `min_three_entities` | Essential definitions require a universe of at least three things |
| `contrast_symmetric_raise_directed` | Contrast is symmetric but raise is not — direction is extra structure |
| `definitions_not_unique` | The same concept can have different essential definitions |
| `chain_depth_bound` | A chain of k definitions accumulates ≥k depth units (hierarchies must terminate) |
| `witness_not_implies_ccd3` | `CCDWitness₃` is strictly weaker than full `CCD₃` |

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
