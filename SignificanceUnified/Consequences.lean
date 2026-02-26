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

-- ══════════════════════════════════════════════════════
-- 16. STRUCTURAL CONSEQUENCES
-- ══════════════════════════════════════════════════════

/-- Genus and differentia are always distinct concepts. If they were equal,
    isEssential would require Raise(genus.χ a)(genus.χ a) = a < a on ℤ,
    which is impossible. Essential definitions always involve genuinely
    different aspects of an entity — the genus and differentia cannot
    collapse into the same concept. -/
theorem KonceptDef.genus_ne_differentia {α : Type} (d : KonceptDef α) :
    d.genus ≠ d.differentia := by
  intro h
  have ha := d.ccd_concept ▸ d.ccd.ha
  exact absurd (h ▸ d.isEssential d.ccd.a ha) (Raise.irrefl _)

/-- The definiendum of an essential definition never includes everything.
    The CCD contrast witness lies outside it. Even the weaker CCDWitness₃
    (not full CCD₃) suffices to rule out universal definienda. -/
theorem KonceptDef.definiendum_not_universal {α : Type} (d : KonceptDef α) :
    ∃ a, ¬d.definiendum.pred a :=
  ⟨d.ccd.contrast, d.ccd_concept ▸ d.ccd.hc⟩

/-- The differentia never includes everything. The CCD contrast witness
    is explicitly required to lack the differentia, meaning the differentia
    always genuinely excludes something — it is a real distinction, not
    a vacuous one. -/
theorem KonceptDef.differentia_not_universal {α : Type} (d : KonceptDef α) :
    ∃ a, ¬d.differentia.pred a :=
  ⟨d.ccd.contrast, d.ccd_contrast⟩

/-- On ℤ, every strict inequality gives a gap of at least 1. -/
private theorem raise_min_gap {a b : ℤ} (h : a < b) : b ≥ a + 1 := by omega

/-- There is a minimum quantum of amplification. On ℤ, every strict raise
    increases the subject by at least 1 above the baseline. Significance
    cannot be raised by an arbitrarily small amount — this is a consequence
    of working over the integers rather than the reals. -/
theorem amplification_min_quantum (m : AmplificationMove) :
    m.comparison.subject ≥ m.comparison.baseline + 1 :=
  raise_min_gap m.isStrict

/-- SimilarByContrast is not transitive. Level comparisons (Raise) compose
    transitively — that is what makes Cicero's chains work. Gap comparisons
    do not. This is the fundamental structural asymmetry between the two
    comparison types.
    Counterexample: 0 and 1 are similar vs 5; 1 and 5 are similar vs 10;
    but 0 and 5 are NOT similar vs 10 because Gap(0,5) = Gap(5,10) = 5,
    violating the strict inequality requirement. -/
theorem similarity_not_transitive :
    ¬(∀ a b c d : Depth,
      SimilarByContrast a b c → SimilarByContrast b c d →
      SimilarByContrast a c d) := by
  intro h
  have h1 : SimilarByContrast (0 : ℤ) 1 5 := by
    refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide
  have h2 : SimilarByContrast (1 : ℤ) 5 10 := by
    refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide
  have h3 := h 0 1 5 10 h1 h2
  obtain ⟨_, _, hlt⟩ := h3
  have hg1 : Gap (0 : ℤ) 5 = 5 := by native_decide
  have hg2 : Gap (5 : ℤ) 10 = 5 := by native_decide
  rw [hg1, hg2] at hlt
  exact absurd hlt (by omega)

/-- The concept preorder is not a partial order. Two concepts with identical
    extensions but different characteristics are mutually ≤ but not equal.
    The ordering sees only which entities fall under each concept; the depth
    scale is invisible to it. This is by design — "all men are animals" is
    about membership, not about depths. -/
theorem preorder_not_partial_order :
    ∃ (k1 k2 : Koncept Unit), k1 ≤ k2 ∧ k2 ≤ k1 ∧ k1 ≠ k2 := by
  refine ⟨⟨fun _ => True, fun _ => 0⟩, ⟨fun _ => True, fun _ => 1⟩,
    fun _ h => h, fun _ h => h, ?_⟩
  intro h
  have := congrFun (congrArg Koncept.χ h) ()
  exact absurd this (by native_decide)

-- ══════════════════════════════════════════════════════
-- 17. DEPTH SCALE PROPERTIES
-- ══════════════════════════════════════════════════════

/-- Gap is definite: zero gap implies equal depths. -/
theorem Gap.eq_of_zero {a b : ℤ} (h : Gap a b = 0) : a = b := by
  unfold Gap at h
  omega

/-- Gap is zero if and only if the two depths are equal. The depth metric
    has no accidental zeros — distinct depths always have positive gap. -/
theorem Gap.eq_zero_iff {a b : ℤ} : Gap a b = 0 ↔ a = b := by
  constructor
  · exact Gap.eq_of_zero
  · rintro rfl; exact Gap.self_zero _

/-- Gap is translation-invariant: shifting both arguments by the same
    amount preserves the gap. Distance on the scale depends only on
    relative position, not absolute placement. -/
theorem Gap.translate {a b k : ℤ} : Gap (a + k) (b + k) = Gap a b := by
  unfold Gap; congr 1; ring

/-- SimilarByContrast is translation-invariant. Adding the same constant to
    all three depth values preserves similarity — the relation depends on
    relative distances, not absolute positions. You can re-zero your depth
    scale anywhere without affecting which things count as similar.
    This means the choice of where zero sits on the depth scale is
    conventional, not structural. -/
theorem SimilarByContrast.translate {a b c k : ℤ}
    (h : SimilarByContrast a b c) :
    SimilarByContrast (a + k) (b + k) (c + k) := by
  obtain ⟨hne, h1, h2⟩ := h
  refine ⟨fun heq => hne (by linarith), ?_, ?_⟩
  · rw [Gap.translate, Gap.translate]; exact h1
  · rw [Gap.translate, Gap.translate]; exact h2

/-- The contrast position in SimilarByContrast is not interchangeable with
    the similar positions. You cannot swap a "similar" entity with the
    contrast entity and preserve the relation. The contrast role is
    structurally distinguished — it is not just another argument.
    Combined with SimilarByContrast.symm (which swaps the first two),
    this shows the relation has exactly the symmetry group S₂, not S₃.
    Counterexample: 0 and 1 are similar vs 5, but 0 and 5 are NOT
    similar vs 1. -/
theorem contrast_not_interchangeable :
    ¬(∀ a b c : Depth, SimilarByContrast a b c → SimilarByContrast a c b) := by
  intro h
  have h1 : SimilarByContrast (0 : ℤ) 1 5 := by
    refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide
  have h2 := h 0 1 5 h1
  obtain ⟨_, hlt, _⟩ := h2
  have hg1 : Gap (0 : ℤ) 5 = 5 := by native_decide
  have hg2 : Gap (0 : ℤ) 1 = 1 := by native_decide
  rw [hg1, hg2] at hlt
  exact absurd hlt (by omega)

/-- The CCD witness gives three pairwise-distinct DEPTH VALUES, not just
    three distinct entities. The depth scale must assign different values
    to all three witness elements. Concept formation requires at least
    three positions on the integer scale. -/
theorem CCDWitness₃.depths_pairwise_distinct {α : Type} (w : CCDWitness₃ α) :
    w.k.χ w.a ≠ w.k.χ w.b ∧
    w.k.χ w.a ≠ w.k.χ w.contrast ∧
    w.k.χ w.b ≠ w.k.χ w.contrast :=
  ⟨w.similar.different,
   w.similar.contrastDiffers_a,
   w.similar.contrastDiffers_b⟩

/-- In any essential definition, the depth scale genuinely separates at
    least two units. The CCD witness entities always have different depths
    under the definiendum's characteristic. The scale is non-degenerate —
    it does real work in distinguishing members of the concept. -/
theorem KonceptDef.depth_separates_units {α : Type} (d : KonceptDef α) :
    d.definiendum.χ d.ccd.a ≠ d.definiendum.χ d.ccd.b := by
  have h := d.ccd.similar.different
  rw [d.ccd_concept] at h
  exact h

/-- A concept with at most one unit satisfies CCD₃ vacuously — there are
    never two distinct units to demand a contrast witness for.
    But such a concept CANNOT be essentially defined, because KonceptDef
    requires a CCDWitness₃ with two distinct units. This reveals the gap
    between CCD₃ (a property any degenerate concept satisfies) and
    definability (which requires substantive grounding). Singletons and
    the empty concept satisfy CCD₃ but are not definable. -/
theorem ccd3_of_subsingleton {α : Type} (k : Koncept α)
    (h : ∀ a b, k.pred a → k.pred b → a = b) : CCD₃ k := by
  intro a b ha hb hab
  exact absurd (h a b ha hb) hab
