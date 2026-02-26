import Basic

/-!
# Surprising Consequences

These theorems are not explicitly stated in the philosophical literature
but fall out of the formalization as necessary consequences of the
structures defined in `Basic.lean`.
-/

-- ══════════════════════════════════════════════════════
-- 14. SURPRISING CONSEQUENCES
-- ══════════════════════════════════════════════════════

/-- "Everything" is not a well-formed concept.
    If a concept's predicate includes every entity of the type (and the type
    has at least two distinct elements), then CCD₃ fails — there is no
    contrast witness outside it.
    Philosophically: concept-formation requires differentiation, and
    differentiation requires something to differentiate FROM. A concept
    that subsumes all of existence has nothing to contrast with, so it
    cannot be grounded. This formalizes the Objectivist principle that
    "existence" is not a concept formed by differentiation. -/
theorem no_universal_ccd {α : Type} (k : Koncept α)
    (huniv : ∀ a, k.pred a) {a b : α} (hab : a ≠ b) : ¬CCD₃ k := by
  intro hccd
  obtain ⟨c, hc, _⟩ := hccd (huniv a) (huniv b) hab
  exact hc (huniv c)

/-- Every essential definition has at least two distinct units.
    You cannot essentially define a singleton concept — concept-formation
    requires observing similarity across at least two instances.
    This formalizes Rand's implicit requirement that abstraction needs
    multiple concretes. It is not assumed — it follows from the CCD
    witness, which must exhibit two distinct entities inside the concept. -/
theorem KonceptDef.has_two_units {α : Type} (d : KonceptDef α) :
    ∃ a b, d.definiendum.pred a ∧ d.definiendum.pred b ∧ a ≠ b :=
  ⟨d.ccd.a, d.ccd.b, d.ccd_concept ▸ d.ccd.ha, d.ccd_concept ▸ d.ccd.hb, d.ccd.hab⟩

/-- In any essential definition, the genus and differentia have strictly
    different characteristic depths on every unit — equal depth would mean
    the differentia adds nothing, contradicting the requirement that it
    explains MORE than the genus.
    This rules out "trivial" definitions where the differentia is
    ornamental rather than explanatory. -/
theorem KonceptDef.genus_lt_differentia {α : Type}
    (d : KonceptDef α) (a : α) (ha : d.definiendum.pred a) :
    d.genus.χ a ≠ d.differentia.χ a :=
  ne_of_lt (d.isEssential a ha)

/-- Amplification is irreversible. If a rhetorical move raises the subject
    above the baseline, the reverse comparison cannot hold on the same scale.
    Once significance is raised, it cannot be un-raised by the same structure.
    This is a structural asymmetry, not a convention — the integers don't
    allow a < b and b < a simultaneously. -/
theorem AmplificationMove.irreversible (m : AmplificationMove) :
    ¬Raise m.comparison.subject m.comparison.baseline :=
  fun h => absurd m.isStrict (not_lt.mpr (le_of_lt h))

/-- Definition chains compose: if the differentia of one definition serves
    as the genus of a refinement, the total depth gain is transitive.
    Concretely: if Man = Rational Animal (rationality > animality) and
    Philosopher = Contemplative Rational (contemplation > rationality),
    then for any philosopher who is also a man, contemplation > animality.
    The depth gain across an entire definitional hierarchy is guaranteed
    by transitivity of <, but this only works because the linking condition
    (d2.genus = d1.differentia) forces the scales to agree at the junction. -/
theorem KonceptDef.chain {α : Type}
    (d1 d2 : KonceptDef α)
    (hchain : d2.genus = d1.differentia)
    (a : α) (ha1 : d1.definiendum.pred a) (ha2 : d2.definiendum.pred a) :
    Raise (d1.genus.χ a) (d2.differentia.χ a) := by
  have r1 := d1.isEssential a ha1
  have r2 := d2.isEssential a ha2
  rw [hchain] at r2
  exact Raise.trans r1 r2

/-- Essential definitions cannot form cycles. If definitions chain through
    their genus/differentia links, a cycle would require a < b < c < a on ℤ,
    which is impossible. The hierarchy of significance is necessarily acyclic.
    This is the deepest consequence: you cannot define A in terms of B,
    B in terms of C, and C back in terms of A — the depth ordering would
    contradict itself. Aristotle's prohibition on circular definition is
    not a methodological preference but a MATHEMATICAL NECESSITY once you
    formalize definitions as carrying strict depth comparisons.
    (Shown here for 3-cycles; the argument generalizes to any length.) -/
theorem no_definition_cycle {α : Type}
    (d1 d2 d3 : KonceptDef α)
    (h12 : d2.genus = d1.differentia)
    (h23 : d3.genus = d2.differentia)
    (h31 : d1.genus = d3.differentia)
    (a : α)
    (ha1 : d1.definiendum.pred a)
    (ha2 : d2.definiendum.pred a)
    (ha3 : d3.definiendum.pred a) : False := by
  have r1 := d1.isEssential a ha1
  have r2 := d2.isEssential a ha2
  have r3 := d3.isEssential a ha3
  rw [h12] at r2
  rw [h23] at r3
  rw [h31] at r1
  exact absurd (Raise.trans (Raise.trans r1 r2) r3) (Raise.irrefl _)

-- ══════════════════════════════════════════════════════
-- 15. FURTHER CONSEQUENCES
-- ══════════════════════════════════════════════════════

/-- The CCD witness exhibits three pairwise-distinct entities: two inside
    the concept and one outside. This means concept theory requires a
    universe of at least three things — with fewer, the entire framework
    is vacuous. -/
theorem CCDWitness₃.three_distinct {α : Type} (w : CCDWitness₃ α) :
    w.a ≠ w.b ∧ w.a ≠ w.contrast ∧ w.b ≠ w.contrast :=
  ⟨w.hab,
   fun h => w.hc (h ▸ w.ha),
   fun h => w.hc (h ▸ w.hb)⟩

/-- Every essential definition requires a universe with at least three
    distinct entities. -/
theorem KonceptDef.min_three_entities {α : Type} (d : KonceptDef α) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  let h := d.ccd.three_distinct
  ⟨d.ccd.a, d.ccd.b, d.ccd.contrast, h.1, h.2.1, h.2.2⟩

/-- Contrast is symmetric but raise is not. SimilarByContrast treats its
    first two arguments interchangeably — swapping "similar" entities
    preserves the relation. Raise does not: a < b does not imply b < a.
    This is why KonceptDef needs isEssential as a separate field: the
    CCD witness determines THAT a raise exists (hasRaise), but not its
    DIRECTION. The choice of which concept is genus and which is
    differentia is additional structure that contrast alone cannot provide. -/
theorem contrast_symmetric_raise_directed :
    (∀ a b c : Depth, SimilarByContrast a b c → SimilarByContrast b a c) ∧
    ¬(∀ a b : Depth, Raise a b → Raise b a) := by
  constructor
  · exact fun _ _ _ h => h.symm
  · intro h
    have := h 0 1 (by show (0 : ℤ) < 1; omega)
    exact absurd this (by show ¬((1 : ℤ) < 0); omega)

/-- Essential definitions of the same concept are not unique. The same
    definiendum can have different genus/differentia decompositions — both
    "Man = Rational Animal" and "Man = Rational Sentient-being" are valid
    essential definitions of the same concept, as long as both genera are
    strictly below the differentia on the depth scale.
    Aristotle sometimes writes as if there is one true definition per
    concept. The formalization shows this is not forced by the structure —
    multiplicity of definitions is consistent with all the axioms. -/
def konceptSentient : Koncept LivingThing :=
  { pred := fun x => match x with
      | .man => True | .human => True | .dog => True | .oak => False
    χ    := fun x => match x with
      | .man => 2 | .human => 2 | .dog => 1 | .oak => 0 }

noncomputable def defManAlt : KonceptDef LivingThing :=
  { definiendum  := konceptMan
    genus        := konceptSentient
    differentia  := konceptRational
    isMeet       := by
      apply Koncept.ext
      · ext a; cases a <;> simp [konceptMan, konceptSentient, konceptRational, Koncept.meet]
      · ext a; cases a <;> simp [konceptMan, konceptSentient, konceptRational, Koncept.meet]
    isEssential  := by
      intro a ha
      cases a with
      | man   => show (2 : ℤ) < 3; omega
      | human => show (2 : ℤ) < 4; omega
      | dog   => exact ha.elim
      | oak   => exact ha.elim
    ccd          := manCCDWitness
    ccd_concept  := rfl
    ccd_contrast := fun h => h }

theorem definitions_not_unique :
    defMan.definiendum = defManAlt.definiendum ∧ defMan.genus ≠ defManAlt.genus := by
  refine ⟨rfl, ?_⟩
  show konceptAnimal ≠ konceptSentient
  intro h
  have := congrFun (congrArg Koncept.χ h) LivingThing.man
  exact absurd this (by native_decide)

/-- Two strict steps on ℤ yield a gap of at least 2. -/
private theorem depth_two_steps {a b c : ℤ} (h1 : a < b) (h2 : b < c) :
    c ≥ a + 2 := by omega

/-- A chain of two definitions accumulates at least 2 units of depth.
    Each essential definition contributes at least 1 (strict inequality on ℤ),
    so k definitions in a chain contribute at least k. On a finite type
    with bounded depth values, this means definition hierarchies must
    terminate — you will eventually exhaust the available depth range.
    This is Aristotle's claim that definition chains bottom out in
    primitive, undefined terms. -/
theorem chain_depth_bound {α : Type}
    (d1 d2 : KonceptDef α)
    (hchain : d2.genus = d1.differentia)
    (a : α) (ha1 : d1.definiendum.pred a) (ha2 : d2.definiendum.pred a) :
    d2.differentia.χ a ≥ d1.genus.χ a + 2 :=
  depth_two_steps (d1.isEssential a ha1)
    ((congrFun (congrArg Koncept.χ hchain) a) ▸ d2.isEssential a ha2)

/-- The CCDWitness₃ used in KonceptDef is strictly weaker than the full
    CCD₃ axiom. Here is a concept with a valid witness for one pair of
    units (.x and .y), but where CCD₃ fails for the pair (.x, .z) —
    their gap (99) exceeds the gap to the only available outsider (.w
    at distance 49 from .x).
    This means a concept can have a valid essential definition (grounded
    by one witnessed pair) without being fully contrast-grounded across
    all pairs of units. Whether full CCD₃ should be required is a genuine
    philosophical question the formalization leaves open. -/
inductive FourThings : Type where
  | x | y | z | w
  deriving DecidableEq, Repr

def weakConcept : Koncept FourThings :=
  { pred := fun t => match t with
      | .x => True | .y => True | .z => True | .w => False
    χ    := fun t => match t with
      | .x => 1 | .y => 2 | .z => 100 | .w => 50 }

def weakWitness : CCDWitness₃ FourThings :=
  { k        := weakConcept
    a        := .x
    b        := .y
    contrast := .w
    ha       := trivial
    hb       := trivial
    hc       := fun h => h
    hab      := by decide
    similar  := by
      refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide }

theorem witness_not_implies_ccd3 : ¬CCD₃ weakConcept := by
  intro hccd
  obtain ⟨c, hc, hsim⟩ := hccd
      (show weakConcept.pred .x from trivial)
      (show weakConcept.pred .z from trivial)
      (by decide : FourThings.x ≠ FourThings.z)
  match c with
  | .x => exact hc trivial
  | .y => exact hc trivial
  | .z => exact hc trivial
  | .w =>
    obtain ⟨_, h1, _⟩ := hsim
    have hg1 : Gap (weakConcept.χ .x) (weakConcept.χ .z) = 99 := by native_decide
    have hg2 : Gap (weakConcept.χ .x) (weakConcept.χ .w) = 49 := by native_decide
    rw [hg1, hg2] at h1
    omega
