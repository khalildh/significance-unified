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

## Multi-dimensional conceptual spaces

`ConceptualSpace.lean` generalizes the depth scale from ℤ to `Point n := Fin n → ℤ` — an n-dimensional space of quality dimensions in the sense of Gärdenfors, with L1 distance. The point of the generalization is a question asked of every theorem in the 1-D theory: **does it survive, or was it an artifact of dimension one?**

**Survives in every dimension** (structural results): translation invariance, the S₂ symmetry of contrast, irreversibility of raises (`RaiseProd.irreversible`), acyclicity of definitions (`no_definition_cycleN`), the minimum quantum (`raiseProd_min_quantum`), genus ≠ differentia, and the two-unit minimum.

**Dies above dimension one** (ℤ-artifacts): *direction from difference*. In 1-D, `a ≠ b` forces a `Raise` in some direction — that was linearity of ℤ, not conceptual structure. In dimension ≥ 2 the product order is partial, and `similar_without_raise_dim2` exhibits a fully valid contrast witness between two incomparable entities: `(0,1)` and `(1,0)` are similar as contrasted with `(5,5)`, yet neither is deeper. `witness_hasRaise_fails` replays this at the concept level. Contrast grounds *grouping*; it cannot ground *direction* once space has two dimensions — so the choice of genus vs differentia is pure extra structure, unrecoverable from contrast even in principle.

**Recovered by choice of weights**: a `DepthFunctional` (positive weighting of the dimensions) collapses the space back to ℤ, and `DepthFunctional.mono` shows every raise in the space becomes a `Raise` on the collapsed scale — the original 1-D theory is the image of the multi-D theory under any such collapse. But `functionals_disagree` shows two weightings can *disagree about direction* on incomparable pairs: which of two concepts is "deeper" is imposed by a weighting, not discovered in the geometry.

## Formal Concept Analysis

`FCA.lean` connects `Koncept` to Mathlib's formal concept analysis (`Mathlib.Order.Concept`, after Ganter & Wille). Any family of Koncepts induces a formal context — entities as objects, concepts as attributes, membership as incidence — and then:

- `extent_attributeConcept` — each Koncept's attribute concept has extent exactly the Koncept's extension: nothing is gained or lost entering the FCA lattice.
- `attributeConcept_le_iff` — the Koncept preorder **is** the concept-lattice order, not merely analogous to it.
- `extent_inf_attributeConcept` — `Koncept.meet` agrees with the lattice-theoretic `⊓`.
- `objectConcept_le_attributeConcept_iff` — the fundamental incidence law: an object concept sits below an attribute concept iff the object has the attribute.

What FCA adds: the concept lattice is *complete* — arbitrary meets and joins exist. What `Koncept` adds that FCA lacks: the characteristic scale χ. FCA sees only membership; significance is the structure FCA forgot.

## Functors between concept categories

The thin-category observation in `CategoryTheory.lean` becomes contentful once functors *between* concept categories enter. `Functors.lean` provides:

- **Change of universe** — `Koncept.comapFunctor : Koncept β ⥤ Koncept α` pulls concepts back along any `f : α → β`, strictly functorially (`comap_id`, `comap_comp`): `Koncept` is a presheaf of preorders on the category of types. Pullback preserves meets (`comap_meet`), essentiality raises (`KonceptDef.raise_comap`), and — the epistemological payload — CCD witnesses (`CCDWitness₃.comap`): contrast-grounding is stable under re-description of the universe.
- **Extension** — the forgetful functor `Koncept α ⥤ Set α` that FCA factors through. It preserves and reflects the order yet is not injective on objects: concepts carry strictly more structure than their extensions, and the surplus is exactly χ.

## Learned embeddings: the audit pipeline

`χ : α → Point n` is an order embedding, and there is a modern ML literature on learning exactly these (Vendrov's order embeddings, Poincaré embeddings, box embeddings). The Lean development gives that literature something it lacks: a **machine-checked specification of what a learned taxonomy must satisfy**. The pipeline in `src/sigml/`:

1. **Train** — `order_embedding_demo.py` learns Vendrov-style order embeddings for a toy taxonomy (numpy SGD).
2. **Place** — each entity is placed on each concept's characteristic scale, quantized to ℤⁿ (matching the spec's decidable integer scales), using the contrast-derived rule described below.
3. **Audit** — `audit.py` mirrors the spec's definitions (`dist₁`, `SimilarByContrastN`, `RaiseProd`, CCD₃, essentiality, the two-unit rule, acyclicity) and reports violations. In the demo run the audit catches a deliberately bad definition (singleton definiendum, incomparable raise) *and* an unplanned pathology — the most general concept's learned characteristic degenerates to zero, so its units cannot be contrast-grounded.
4. **Certify** — the passing subset is emitted as `SignificanceUnified/AuditCert.lean`, where certified definitions are literally *terms of* `KonceptDefN` with every proof closed by `decide`. `lake build` is the final judge: the Lean kernel, not the Python code, certifies that the learned structure satisfies the spec.

```bash
.venv/bin/python src/sigml/order_embedding_demo.py   # train + audit + emit
lake build                                            # kernel-check the certificate
```

Audit violations are the interesting output: a CCD₃ failure means a learned class doesn't cluster against any outsider; an essentiality failure means a genus/differentia pair whose depths are incomparable; a two-unit failure means a class that should be an individual. This is the OntoClean-style use case — taxonomy auditing — with the audit criteria proved rather than postulated.

### Contrast-derived characteristic scales

`Basic.lean` says choosing which characteristic defines χ is "the hard epistemological problem — the formalization assumes it is solved externally." `ContrastScale.lean` stops assuming it, following Rand's Conceptual Common Denominator (with Tversky's diagnosticity and Gärdenfors's dimension salience as the modern analogues): **the scale on which a concept measures its units is the scale on which its units differ from their foil.** Given a shared placement of entities, a concept's diagnostic weighting is the member-vs-foil separation on each dimension (`diagWeightIn`), and its derived characteristic weights each entity's position by that diagnosticity (`contrastChiIn`). For a differentia, the theoretically correct foil is the *rest of its genus* — the foil for `rational` in defining Man is the other animals, not the oak (Aristotle: the differentia divides the genus).

What becomes provable once the scale is constructed rather than assumed:

- **"Everything" has no scale, not just no witness** (`universal_no_derived_similarity`) — a universal concept has an empty foil, so its derived characteristic is the zero scale and no similarity judgment can even be stated on it. This strengthens `no_universal_ccd`: Rand's claim that "existence" has no CCD, as a theorem.
- **Ornamental differentiae have no scale** (`ornamental_differentia_no_scale`) — a differentia that excludes nothing from its genus measures nothing: the scale-level version of `genus_ne_differentia`.
- **Meaningfulness** (`diagWeightIn_translate`, `contrastChiIn_dist_translate`) — diagnostic weights and derived-scale distances are invariant under translation of the underlying positions, extending `Gap.translate` from raw scales to the entire scale-construction procedure.
- **Grounding without direction persists** (`beastie_derived_ccd`, `beastie_derived_no_direction`) — deriving the scale from contrast buys grounding, but the incomparable pair stays incomparable: direction remains extra structure even on the concept's own scale.

The demo runs both placement rules and compares. Findings from the switch:

- **The `animal` degeneracy was partly an artifact of the old rule** — under contrast-derived scales, animal's characteristic is non-degenerate and 4 of 15 unit pairs get grounded (against the lone outsider, the oak). The remaining failures are informative: with a single outsider and heterogeneous units, full CCD₃ is very demanding — as a concept approaches universality, its foil thins and grounding erodes, the finite shadow of `no_universal_ccd`.
- **Omitted measurements can erase units** — `rational`'s derived scale zeroes the one dimension its two units differ on (it isn't diagnostic of rationality against the other animals), collapsing socrates and hypatia to the same point, so the concept fails CCD₃ *on its own scale*: a `depth_separates_units` violation produced by the scale-construction itself.
- **Incommensurability is real and detected** — the strict product-order raise (`RaiseProd`) essentially never holds across two concepts' differently-sparse attention weightings; Rand's requirement that the CCD be a *common* denominator reappears as a commensuration obligation (the demo normalizes all weightings to equal total attention). Even commensurated, `human = rational animal` fails the product raise but **holds under the uniform depth functional on every unit** — so the certificate records the weaker, explicitly weighting-dependent claim (`human_functional_essential`), exactly the direction-is-imposed reading that `functionals_disagree` warns about. The deliberately bad `dog = domestic canid` fails even the functional collapse: the audit now grades definitions (strong product raise / weak functional raise / nothing) instead of passing them binarily.

### The shared CCD

`SharedCCD.lean` ties off the two loose ends the findings above opened.

**Only the ray matters.** The pipeline ships *normalized* weights while the `ContrastScale` theorems speak of raw ones. `similarByContrastN_smul_iff` and `raiseProd_smul_iff` close that gap: every single-scale audit predicate is invariant under uniform positive rescaling of the weighting, so any common-total representative of a weighting ray is as good as any other. The converse — `raise_flips_under_independent_rescale` — is the incommensurability finding as a theorem: a raise across two *independent* scales flips under transformations each scale is defined up to. Cross-scale essentiality is measurement-theoretically meaningless without a shared unit; that is what "conceptual **common** denominator" means, formally.

**`KonceptDefCCD`.** Accordingly, the spec gains a strengthened essential-definition structure: one shared entity placement, two attention profiles with *equal total attention* (`commensurate`), and proofs that the genus and differentia characteristics are exactly the weighted placements. Its essentiality verdict is provably invariant under change of the common unit (`KonceptDefCCD.essential_rescale`), and every `KonceptDefCCD` forgets to a `KonceptDefN` (`toKonceptDefN`), so the revision strengthens the spec without forking it. Certificates now emit `KonceptDefCCD` terms when a definition passes strict essentiality — `AuditCertSynthetic.lean` (generated by `synthetic_cert_test.py`) exercises the full strong path; the learned demo currently earns the functional grade.

**The measurement-omission question, adjudicated.** The `rational`-collapse finding forced a choice: when a derived scale erases the difference between a concept's units, is that a defect or is it Rand's "measurement omission" working as intended? Decision: the spec is right and stays — Rand's own doctrine is that units possess the CCD characteristic in *different* measure or degree (the `a ≠ b` conjunct of `SimilarByContrast`, `depth_separates_units`), and "no two existents are identical in measurement" makes a collapse an artifact of insufficient resolution, not a fact about the entities. The pipeline therefore treats collapse as a signal to *increase measurement resolution* (adaptive quantization: the demo detects the `rational` collapse at 1/4 and resolves it at 1/8, after which `rational` passes CCD₃); only a collapse persisting at the resolution cap counts against the concept.

## First real-data slice: WordNet Carnivora

`src/sigml/wordnet_slice.py` runs the audit against real lexical structure — a
WordNet noun subtree rather than a toy or synthetic ontology. WordNet supplies
only hypernymy (is-a), so this slice tests the **grounding layer** — CCD₃
clustering, the subsumption preorder, acyclicity — and deliberately not
essentiality (WordNet has no differentiae; that question stays open). The
subtree is Carnivora, chosen because the repository's running example is
dog/wolf/cat and this is the real version: Canidae, Felidae, Ursidae,
Mustelidae, Procyonidae, ~37 species at genus granularity.

Every CCD₃ verdict has two possible causes — a real gap in the taxonomy, or an
artifact of how entities were embedded — so the slice runs **two independent
position sources** and cross-tabulates: trained order embeddings (torch,
8 seeds, reported as mean over seeds) and a deterministic structural control
(per-synset graph features, no training). Agreement between them attributes a
verdict to the taxonomy; divergence attributes it to the representation.

Result (CCD₃ pairs grounded, within-family, against out-family outsiders):

| Family | Trained (mean) | Structural control | Reading |
|--------|:---:|:---:|---|
| canine | 0.96 | 0.67 | trained-only — the embedding recovers coherence bare structure misses |
| feline | 0.87 | 0.76 | partial under both (~81%) — structural |
| bear | 0.86 | 0.90 | partial under both (~88%) — structural |
| musteline | 0.79 | 0.87 | partial under both (~83%) — structural |
| procyonid | 0.83 | 0.80 | partial under both (~82%) — structural |

What the slice actually shows:

1. **CCD₃ has teeth without being absurd.** ~80–96% of member pairs ground; the criterion is neither trivially satisfied nor obviously wrong on real data — the honest outcome you want from a first slice. It is a substantive constraint that real lexical concepts *mostly but not fully* meet.
2. **The failures localize real heterogeneity.** The ungrounded residue concentrates in the "wastebasket" families — Mustelidae (weasels, badgers, otters, skunks) and Procyonidae (raccoons *and* pandas) — taxa that are morphologically diverse and cohere worse against outsiders. The audit flags exactly the families a taxonomist would call heterogeneous.
3. **The cross-source safeguard worked.** On four of five families the two independent position sources agree within ~0.15, attributing grounding to the taxonomy rather than the embedding. The exception is Canidae, where the trained embedding grounds (0.96) far above the structural control (0.67): a case where learning recovers conceptual coherence that bare graph structure does not encode — bare hierarchy is symmetric under sibling exchange, so a purely structural embedding has weak within-family resolution.
4. **A WordNet-sourced grounding certificate kernel-checks.** `AuditCertWordNet.lean` (the dog·wolf / lion·tiger core, quantized to ℤ⁵) inhabits the spec and closes its CCD₃ proofs by `decide`.

Honest limits: grounding layer only (essentiality needs a corpus with differentiae — an OBO ontology is the natural next target); 5-dimensional embeddings on a single subtree of a few dozen species; `CAP=10` members per family, with dropped members logged, not silently truncated. This is a proof that the pipeline runs on real data and produces interpretable, taxonomy-attributable findings — not a WordNet-wide claim.

```bash
pip install torch nltk                         # wordnet corpus auto-downloads
.venv/bin/python src/sigml/wordnet_slice.py   # audit + cross-tab + emit cert
lake build                                     # kernel-check AuditCertWordNet.lean
```

## The essentiality question: real definitions from the Cell Ontology

The WordNet slice could not test essentiality — WordNet has no differentiae.
OBO Foundry ontologies are built on Aristotelian definitions: every defined
term carries a logical definition `T = genus ∩ (R some F)`. The Cell Ontology
(`cl.obo`) has ~1,700 such terms. `src/sigml/obo_slice.py` finally puts the
essentiality layer — `KonceptDefN`/`KonceptDefCCD` — in front of real
ontological definitions, and asks of each: does the differentia sit **strictly
deeper** than the genus (strict `RaiseProd`, the spec's `isEssential`), only
under equal attention (the weak uniform-**functional** grade), or **neither**?

Across 10 real CL definitions (majority grade over 6 seeds, contrast-derived
commensurated scales, order embeddings on the is-a graph):

| Grade | Count | |
|---|:---:|---|
| strict `RaiseProd` essentiality | **0** | as the theory predicts — see below |
| functional grade only | 5 | differentia outweighs genus under equal attention |
| neither | 5 | genus outweighs differentia even under equal attention |

Three honest readings, in order of importance:

1. **The strict result is the theorem, not biology.** `functionals_disagree`
   and `SharedCCD`'s rescaling lemmas already imply that a strict product-order
   raise between two *commensurated* weightings is near-structurally impossible
   (both weightings sum to the same total attention, so per-dimension dominance
   forces equality). Finding 0/10 strict on real data is that theorem
   reappearing — it is *not* evidence about the Cell Ontology, and reporting it
   as such would be a mistake. Strict `RaiseProd` is the wrong bar for learned
   definitions.

2. **Under the operative (functional) bar, the signal is weak and split.**
   Half the definitions reach the functional grade, half do not — but many sit
   at 3/3 coin-flips across seeds, so the differentia does *not robustly*
   outweigh the genus. The learned essentiality signal hovers at the decision
   boundary.

3. **Why: CL definitions are marker refinements, not depth-ordered essences.**
   The definitions the slice surfaces are things like *CD38-positive IgG memory
   B cell*, *Gr1-high classical monocyte*, *enucleated reticulocyte*. The
   differentia is a molecular **marker** or a fine feature that adds
   discrimination without being "deeper" than the genus in any measurement
   sense. This is a genuine mismatch: the formalization encodes Aristotelian
   essentialism (differentia strictly deeper than genus), while contemporary
   bio-ontologies define terms **compositionally and additively**. The spec's
   notion of essence does not fit how real ontologies are built.

This points at a spec revision the earlier PRs already set up: `isEssential`
should perhaps be the **weighting-relative** condition (there *exists* a
positive functional under which the differentia is deeper for every unit),
which is weaker, achievable, and more faithful to Rand's context-relative
account of essence — exactly the reading `functionals_disagree` formalizes. The
OBO data is evidence for that revision rather than for the strict product
order. `AuditCertOBO.lean` records one real CL definition at the functional
grade (entities are CL term IDs, quantized to ℤ⁶, proof by `decide`).

Honest limits: 10 definitions from one ontology, 6-dimensional embeddings; the
differentia-membership model (`R some F` → entities with an R-edge to F) is a
modeling choice and a confound; selection favors tractably-small definitions,
which are disproportionately marker refinements — larger structural definitions
are untested. This is a first, deliberately humbling look at the essentiality
layer on real data, not a verdict on OBO ontologies.

```bash
.venv/bin/python src/sigml/obo_slice.py   # grades real CL definitions; cl.obo auto-downloads
lake build                                 # kernel-checks AuditCertOBO.lean
```

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
├── Basic.lean            # Core formalization (sections 1–13)
├── Consequences.lean     # Derived theorems (sections 14–19)
├── CategoryTheory.lean   # Categorical reformulation (thin categories)
├── ConceptualSpace.lean  # Multi-dimensional generalization (ℤ → ℤⁿ)
├── ContrastScale.lean    # Contrast-derived characteristic scales (the CCD, constructed)
├── SharedCCD.lean        # Rescaling invariance + commensurate essentiality (KonceptDefCCD)
├── FCA.lean              # Bridge to Mathlib formal concept analysis
├── Functors.lean         # Functors between concept categories
├── AuditCert.lean        # Machine-generated certificate (toy demo)
├── AuditCertSynthetic.lean # Machine-generated: full KonceptDefCCD path fixture
├── AuditCertWordNet.lean # Machine-generated: WordNet Carnivora grounding core
└── AuditCertOBO.lean     # Machine-generated: a real Cell-Ontology definition
src/sigml/
├── audit.py                  # Spec mirror + Lean certificate emission
├── order_embedding_demo.py   # Train → place → audit → certify (toy)
├── synthetic_cert_test.py    # Exercises the strong (KonceptDefCCD) certificate path
├── wordnet_slice.py          # Real-data slice: WordNet Carnivora grounding audit
└── obo_slice.py              # Real-data slice: Cell-Ontology essentiality grades
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
- **L1 distance and the product order in ℤⁿ**: Both keep the multi-dimensional theory decidable, so `decide` closes concrete goals — including every proof in the machine-generated `AuditCert.lean`. The product order (rather than a lexicographic or weighted order) is what makes incomparability representable, which is the philosophical point of the generalization.
- **Certificates over trust**: The Python auditor is deliberately treated as untrusted. Its only job is to *find* witnesses; the emitted Lean file re-proves everything by `decide`, so the kernel is the arbiter.
