import Basic
import Mathlib.Order.Concept

/-!
# Bridge to Formal Concept Analysis

Formal Concept Analysis (Ganter & Wille) is the established lattice-theoretic
theory of concepts: a *formal context* is a relation between objects and
attributes, and a *formal concept* is a Galois-closed pair (extent, intent).
Mathlib formalizes this in `Mathlib.Order.Concept`.

This file connects `Koncept` to that machinery. Any family of Koncepts over
a universe `α` induces a formal context: objects are entities, attributes are
the concepts themselves, incidence is membership. Then:

1. Every Koncept yields an **attribute concept** in the FCA lattice, whose
   extent is exactly the Koncept's extension (`extent_attributeConcept`).
2. The Koncept preorder is exactly the concept-lattice order on attribute
   concepts (`attributeConcept_le_iff`) — subsumption is not merely
   *analogous* to the FCA order, it *is* the FCA order.
3. `Koncept.meet` agrees with the lattice-theoretic `⊓`
   (`extent_inf_attributeConcept`).
4. The fundamental FCA incidence law holds: an object concept lies below an
   attribute concept iff the object has the attribute
   (`objectConcept_le_attributeConcept_iff`).

What FCA adds that the raw preorder lacks: the concept lattice is a
**complete lattice** — arbitrary meets and joins exist, closing the concept
space under conjunction and disjunction of any family. What `Koncept` adds
that FCA lacks: the characteristic scale χ. FCA sees only membership;
significance is the structure FCA forgot.
-/

open Set

variable {α : Type} {ι : Type}

/-- The formal context induced by a family of Koncepts: entities are
    objects, the concepts are attributes, incidence is membership. -/
def Koncept.memRel (K : ι → Koncept α) : α → ι → Prop :=
  fun a i => (K i).pred a

/-- The attribute concept of `K i` in the FCA lattice: the Galois closure
    of the single attribute `i`. -/
def attributeConcept (K : ι → Koncept α) (i : ι) :
    Concept α ι (Koncept.memRel K) where
  extent := lowerPolar (Koncept.memRel K) {i}
  intent := upperPolar (Koncept.memRel K) (lowerPolar (Koncept.memRel K) {i})
  upperPolar_extent := rfl
  lowerPolar_intent := lowerPolar_upperPolar_lowerPolar _ _

/-- The object concept of an entity `a`: the Galois closure of the single
    object `a`. -/
def objectConcept (K : ι → Koncept α) (a : α) :
    Concept α ι (Koncept.memRel K) where
  extent := lowerPolar (Koncept.memRel K) (upperPolar (Koncept.memRel K) {a})
  intent := upperPolar (Koncept.memRel K) {a}
  upperPolar_extent := upperPolar_lowerPolar_upperPolar _ _
  lowerPolar_intent := rfl

/-- The extent of the attribute concept is exactly the Koncept's extension:
    nothing is gained or lost passing into the FCA lattice. -/
theorem extent_attributeConcept (K : ι → Koncept α) (i : ι) :
    (attributeConcept K i).extent = (K i).extension := by
  ext a
  simp [attributeConcept, lowerPolar, Koncept.memRel, Koncept.extension]

/-- The intent of the object concept is the set of concepts the entity
    falls under. -/
theorem intent_objectConcept (K : ι → Koncept α) (a : α) :
    (objectConcept K a).intent = { i | (K i).pred a } := by
  ext i
  simp [objectConcept, upperPolar, Koncept.memRel]

/-- **Subsumption is the concept-lattice order.** The Koncept preorder
    (`K i ≤ K j` iff every unit of `K i` is a unit of `K j`) coincides with
    the FCA lattice order on attribute concepts. -/
theorem attributeConcept_le_iff {K : ι → Koncept α} {i j : ι} :
    attributeConcept K i ≤ attributeConcept K j ↔ K i ≤ K j := by
  rw [← Concept.extent_subset_extent_iff,
    extent_attributeConcept, extent_attributeConcept]
  exact Iff.rfl

/-- `Koncept.meet` agrees with the lattice-theoretic meet: the extent of
    `⊓` in the concept lattice is the extension of the Koncept meet. -/
theorem extent_inf_attributeConcept (K : ι → Koncept α) (i j : ι) :
    (attributeConcept K i ⊓ attributeConcept K j).extent
      = ((K i).meet (K j)).extension := by
  rw [Concept.extent_inf, extent_attributeConcept, extent_attributeConcept]
  ext a
  simp [Koncept.meet, Koncept.extension]

/-- **The fundamental incidence law of FCA**: the object concept of `a`
    lies below the attribute concept of `i` exactly when `a` falls under
    `K i`. Membership is recovered from the lattice order alone. -/
theorem objectConcept_le_attributeConcept_iff {K : ι → Koncept α}
    {a : α} {i : ι} :
    objectConcept K a ≤ attributeConcept K i ↔ (K i).pred a := by
  rw [← Concept.extent_subset_extent_iff]
  constructor
  · intro h
    have ha : a ∈ (objectConcept K a).extent :=
      subset_lowerPolar_upperPolar _ {a} rfl
    have hmem := h ha
    rw [extent_attributeConcept] at hmem
    exact hmem
  · intro hpred
    show lowerPolar _ (upperPolar _ {a}) ⊆ lowerPolar _ {i}
    apply lowerPolar_anti
    intro j hj
    rcases hj with rfl
    intro x hx
    rcases hx with rfl
    exact hpred

/-- The concept lattice is complete: arbitrary meets and joins of concepts
    exist. This is the closure property the bare `Koncept` preorder lacks —
    FCA supplies it for free. -/
example (K : ι → Koncept α) :
    CompleteLattice (Concept α ι (Koncept.memRel K)) := inferInstance

-- ══════════════════════════════════════════════════════
-- CONCRETE: THE MAN/ANIMAL/RATIONAL CONTEXT
--
--    The running example from Basic.lean, replayed inside the
--    FCA lattice. Attributes: 0 = Man, 1 = Animal, 2 = Rational.
-- ══════════════════════════════════════════════════════

def stdFamily : Fin 3 → Koncept LivingThing :=
  ![konceptMan, konceptAnimal, konceptRational]

/-- "All men are animals," as an inequality of formal concepts. -/
theorem manConcept_le_animalConcept :
    attributeConcept stdFamily 0 ≤ attributeConcept stdFamily 1 :=
  attributeConcept_le_iff.mpr all_men_are_animals

/-- "All men are rational," as an inequality of formal concepts. -/
theorem manConcept_le_rationalConcept :
    attributeConcept stdFamily 0 ≤ attributeConcept stdFamily 2 :=
  attributeConcept_le_iff.mpr all_men_are_rational

/-- The intent of the object concept of `man` is {Man, Animal, Rational}:
    reading an entity's full attribute set off the Galois connection. -/
theorem man_intent :
    (objectConcept stdFamily .man).intent = Set.univ := by
  rw [intent_objectConcept]
  ext i
  fin_cases i <;> simp [stdFamily, konceptMan, konceptAnimal, konceptRational]

/-- The oak falls under no concept in the family: its object concept's
    intent is empty. -/
theorem oak_intent :
    (objectConcept stdFamily .oak).intent = ∅ := by
  rw [intent_objectConcept]
  ext i
  fin_cases i <;> simp [stdFamily, konceptMan, konceptAnimal, konceptRational]
