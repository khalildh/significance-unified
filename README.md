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

## The square of opposition

The formalization defines the four categorical propositions and proves all six classical relationships between them:

- **PropA** (universal affirmative): All S are P — `S ≤ P`
- **PropE** (universal negative): No S are P — `∀ a, S.pred a → ¬P.pred a`
- **PropI** (particular affirmative): Some S are P — `∃ a, S.pred a ∧ P.pred a`
- **PropO** (particular negative): Some S are not P — `∃ a, S.pred a ∧ ¬P.pred a`

The relationships:

- **Contradiction**: A ↔ ¬O and E ↔ ¬I. The E-I contradiction is fully constructive; A-O needs Classical for the ¬O → A direction (double negation elimination on `P.pred a`).
- **Contrariety**: A and E cannot both hold when S is non-empty.
- **Subalternation**: A → I and E → O, both requiring a non-empty subject. For essentially defined concepts, the CCD witness provides the existential automatically — subalternation always fires.
- **Subcontrariety**: I and O cannot both fail when S is non-empty. The proof is constructive: ¬I gives ¬P.pred a, ¬O gives ¬¬P.pred a, contradiction.

## Complete syllogistic

The formalization proves all 15 unconditionally valid syllogistic moods across all four figures, plus 4 moods requiring existential import — the entire classical syllogistic as a verified consequence of the concept preorder. Every proof is 2-3 lines.

| Figure | Mood | Type | Notes |
|--------|------|------|-------|
| 1 | Barbara (AAA) | A | Transitivity of ≤ |
| 1 | Celarent (EAE) | A | |
| 1 | Darii (AII) | A | |
| 1 | Ferio (EIO) | A | |
| 2 | Cesare (EAE) | A | |
| 2 | Camestres (AEE) | A | |
| 2 | Festino (EIO) | A | |
| 2 | Baroco (AOO) | A | Traditionally needs reductio; direct here |
| 3 | Disamis (IAI) | A | |
| 3 | Datisi (AII) | A | |
| 3 | Bocardo (OAO) | A | Traditionally needs reductio; direct here |
| 3 | Ferison (EIO) | A | |
| 4 | Camenes (AEE) | A | |
| 4 | Dimaris (IAI) | A | |
| 4 | Fresison (EIO) | A | |
| 3 | Darapti (AAI) | E | Requires non-empty M |
| 3 | Felapton (EAO) | E | Requires non-empty M |
| 4 | Bramantip (AAI) | E | Requires non-empty P |
| 4 | Fesapo (EAO) | E | Requires non-empty M |

Type A = unconditionally valid. Type E = requires existential import.

Baroco and Bocardo are notable: traditional logic proves them by *reductio ad absurdum*, but in this formalization they are direct — destructure the existential witness and apply the universal premise. No contradiction needed.

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

### Genus and differentia must be distinct

`KonceptDef.genus_ne_differentia` — If genus = differentia, then `isEssential` would require `a < a` on ℤ, which is impossible. Essential definitions always involve genuinely different aspects of an entity.

### Neither definiendum nor differentia can be universal

`definiendum_not_universal` and `differentia_not_universal` — The CCD contrast witness lies outside the definiendum and lacks the differentia. Both the defined concept and its distinguishing property always genuinely exclude something.

### Significance is quantized

`amplification_min_quantum` — On ℤ, every strict raise increases the subject by at least 1 above the baseline. There is a smallest possible unit of amplification. If we used ℝ instead, raises could be arbitrarily small.

### Gap comparison does not compose

`similarity_not_transitive` — Level comparisons (Raise) compose transitively; gap comparisons (SimilarByContrast) do not. Concrete counterexample: 0 and 1 are similar vs 5, and 1 and 5 are similar vs 10, but 0 and 5 are NOT similar vs 10 (Gap(0,5) = Gap(5,10) = 5, violating strict inequality). This is the formal proof that the two comparison types have fundamentally different algebraic structure — the reason the formalization must keep them separate.

### The concept preorder is genuinely a preorder

`preorder_not_partial_order` — Two concepts with the same extension but different depth scales are mutually ≤ but not equal. The ordering sees only membership, not depths. This is by design: "all men are animals" is about which things fall under each concept, not about their characteristic values.

### Similarity is about relative position

`Gap.translate` and `SimilarByContrast.translate` — Gap and similarity are both translation-invariant. Adding the same constant to all depth values preserves which things are similar and which are different. The zero-point of the depth scale is conventional, not structural.

### The contrast position is structurally distinguished

`contrast_not_interchangeable` — You cannot swap a "similar" entity with the contrast entity and preserve the relation. Combined with `SimilarByContrast.symm` (swapping the two similar things is fine), this shows the relation has symmetry group S₂, not S₃. The outsider plays a genuinely different role from the insiders.

### Concept formation needs three depth values

`CCDWitness₃.depths_pairwise_distinct` and `KonceptDef.depth_separates_units` — CCD witnesses give three pairwise-distinct depth values, not just three distinct entities. The depth scale must have at least three positions. And within any defined concept, at least two units have different depths — the scale is non-degenerate.

### CCD₃ is necessary but not sufficient for definability

`ccd3_of_subsingleton` — A concept with at most one unit satisfies CCD₃ vacuously (there are never two distinct units to ask about). But such a concept cannot be essentially defined — `KonceptDef` requires a CCD witness with two distinct units. This reveals the gap between satisfying CCD₃ (which degenerate concepts do trivially) and being definable (which requires substantive grounding).

### The meta-point

These 27 results were previously **separate doctrines** from different authors and different centuries — Aristotle's anti-circularity, Aristotle's "being is not a genus," Rand's "two or more concretes," the compositionality and termination of definitional hierarchies, the non-uniqueness of definitions, the structural difference between level and gap comparisons, the distinguished role of the contrast witness, the translation invariance of similarity, and the quantization of significance. The formalization shows they are all consequences of one thing: **essential definitions carry a strict depth comparison grounded in contrast on an integer scale**. That is the unification — not just Kennedy and Rand, but the downstream implications that were never connected before.

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
└── Consequences.lean   # Derived theorems (sections 14–19)
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
| `genus_ne_differentia` | Genus and differentia must always be distinct concepts |
| `definiendum_not_universal` | The defined concept never includes everything |
| `differentia_not_universal` | The differentia always genuinely excludes something |
| `amplification_min_quantum` | Every raise is by at least 1 — significance is quantized on ℤ |
| `similarity_not_transitive` | Gap comparison does NOT compose transitively (counterexample) |
| `preorder_not_partial_order` | The concept ordering is a genuine preorder, not a partial order |
| `Gap.eq_zero_iff` | Zero gap if and only if equal depths (metric is definite) |
| `Gap.translate` | Gap is translation-invariant |
| `SimilarByContrast.translate` | Similarity is translation-invariant — the zero-point is conventional |
| `contrast_not_interchangeable` | The contrast role is structurally distinguished (symmetry S₂, not S₃) |
| `depths_pairwise_distinct` | CCD witnesses give three distinct depth values, not just entities |
| `depth_separates_units` | The depth scale genuinely separates units within every defined concept |
| `ccd3_of_subsingleton` | Singletons satisfy CCD₃ vacuously but cannot be essentially defined |
| `propA_iff_not_propO` | A and O are contradictories (Classical for one direction) |
| `propE_iff_not_propI` | E and I are contradictories (fully constructive) |
| `contrary` | A and E cannot both hold for non-empty subjects |
| `subalternation_AI` | A → I when subject is non-empty |
| `subalternation_EO` | E → O when subject is non-empty |
| `subcontrary` | I and O cannot both fail for non-empty subjects |
| `existential_import` | CCD witness guarantees non-empty definiendum |
| `ferio` | Ferio (EIO-1) |
| `cesare` | Cesare (EAE-2) |
| `camestres` | Camestres (AEE-2) |
| `festino` | Festino (EIO-2) |
| `baroco` | Baroco (AOO-2) — direct, no reductio needed |
| `disamis` | Disamis (IAI-3) |
| `datisi` | Datisi (AII-3) |
| `bocardo` | Bocardo (OAO-3) — direct, no reductio needed |
| `ferison` | Ferison (EIO-3) |
| `camenes` | Camenes (AEE-4) |
| `dimaris` | Dimaris (IAI-4) |
| `fresison` | Fresison (EIO-4) |
| `darapti` | Darapti (AAI-3) — requires existential import |
| `felapton` | Felapton (EAO-3) — requires existential import |
| `bramantip` | Bramantip (AAI-4) — requires existential import |
| `fesapo` | Fesapo (EAO-4) — requires existential import |

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
