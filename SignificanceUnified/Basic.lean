import Mathlib.Tactic
import Mathlib.Data.Set.Basic

/-!
# Significance as a Preorder — A Unified Formalization

## Two comparison primitives, one scale

Both Kennedy and Rand are working from the same underlying integer scale:
  χ : α → ℤ   (degree of possession of a characteristic)

But concept-formation requires TWO kinds of comparison on that scale, not one:

**Level comparison** (significance / explanatory depth)
  `Raise χ a b` iff `χ a < χ b`
  Used for: "differentia explains more than genus," "sacrilege > theft"
  Structure: strict order, composes transitively (Cicero's chain)

**Gap comparison** (contrast / differentiation)
  `SimilarByContrast (χ a) (χ b) (χ c)` iff `|χ a - χ b| < |χ a - χ c|` and `|χ a - χ b| < |χ b - χ c|`
  Used for: "dogs and wolves are similar compared to cats"
  Structure: ternary, relative — does NOT compose like raises

Forcing both into `SignificanceRaise` would conflate them and produce wrong
transitivity/composition claims for contrast. Keeping them separate lets each
have only the structure it actually has.

## What this file proves

1. `AmplificationMove` embeds into `SignificanceRaise` (total function, level comparison).
2. `KonceptDef` embeds into `SignificanceRaise` per unit (total function, level comparison).
3. `AmplificationOver` round-trips through `KonceptDefWithUnit` (honest bijection on concept fields).
4. From the explicit "different degree" conjunct of `SimilarByContrast`, a `Raise` in some
   direction follows by linearity of ℤ. The gap inequalities do not themselves give direction.
5. `CCD₃` axiomatizes contrast-grounded differentiation (one integer scale per concept).

## Naming notes
  `attribute` → `pred`
  `concept`   → `Koncept`
-/

-- ══════════════════════════════════════════════════════
-- 1. ONE SCALE, TWO INDUCED COMPARISONS
-- ══════════════════════════════════════════════════════

abbrev Depth := ℤ
abbrev Characteristic (α : Type) := α → Depth

/-- Level comparison: b is strictly deeper than a on this scale. -/
def Raise (a b : Depth) : Prop := a < b

-- Raise is a strict order
theorem Raise.trans {a b c : Depth} (h1 : Raise a b) (h2 : Raise b c) :
    Raise a c := Int.lt_trans h1 h2

theorem Raise.irrefl (a : Depth) : ¬Raise a a := lt_irrefl a

-- Alias kept for backward compat with rest of file
def StrictComparison := Raise

theorem strict_trans {a b c : Depth}
    (h1 : StrictComparison a b) (h2 : StrictComparison b c) :
    StrictComparison a c := Raise.trans h1 h2

/-- Gap: absolute difference between two depth values, as ℕ via Int.natAbs.
    Returns ℕ (not ℤ) so gap comparisons use < on ℕ throughout.
    a and b here are χ-values (depths), not entities. -/
def Gap (a b : Depth) : ℕ := Int.natAbs (a - b)

theorem Gap.symm (a b : Depth) : Gap a b = Gap b a := by
  simp only [Gap]
  have h : b - a = -(a - b) := by abel
  rw [h, Int.natAbs_neg]

theorem Gap.self_zero (a : Depth) : Gap a a = 0 := by simp [Gap]

/-- Gap comparison: b is closer to a than c is. -/
def Closer (a b c : Depth) : Prop := Gap a b < Gap a c

/-- Ternary similarity: a and b are similar as contrasted with c.
    Note: a, b, c here are χ-VALUES (depths on ℤ), not entities.
    The condition has three conjuncts:
      (1) a ≠ b  — Rand's "different measure or degree," EXPLICIT.
                   The gap inequalities alone do NOT imply this:
                   if a = b then Gap a b = 0 < Gap a c is consistent.
      (2) Gap a b < Gap a c  — a and b closer to each other than a is to c
      (3) Gap a b < Gap b c  — and closer than b is to c
    This is "dogs and wolves similar compared to cats" on the depth scale. -/
def SimilarByContrast (a b c : Depth) : Prop :=
  a ≠ b ∧ Gap a b < Gap a c ∧ Gap a b < Gap b c

theorem SimilarByContrast.symm {a b c : Depth} (h : SimilarByContrast a b c) :
    SimilarByContrast b a c := by
  obtain ⟨hne, h1, h2⟩ := h
  refine ⟨hne.symm, ?_, ?_⟩
  · rw [Gap.symm b a]; exact h2
  · rw [Gap.symm b a]; exact h1

theorem SimilarByContrast.different {a b c : Depth} (h : SimilarByContrast a b c) :
    a ≠ b := h.1

theorem SimilarByContrast.contrastDiffers_a {a b c : Depth}
    (h : SimilarByContrast a b c) : a ≠ c := by
  intro heq; subst heq
  obtain ⟨_, hlt, _⟩ := h
  simp [Gap] at hlt

theorem SimilarByContrast.contrastDiffers_b {a b c : Depth}
    (h : SimilarByContrast a b c) : b ≠ c := by
  intro heq; subst heq
  obtain ⟨_, _, hlt⟩ := h
  simp [Gap] at hlt

/-- From the explicit "different degree" conjunct of SimilarByContrast,
    we can derive a Raise in one direction or the other (by linearity of ℤ).
    Note: this uses ONLY the a ≠ b conjunct, not the gap inequalities.
    The contrast structure does not itself generate direction — that requires
    the non-degeneracy assumption. -/
theorem SimilarByContrast.hasRaise {a b c : Depth} (h : SimilarByContrast a b c) :
    Raise a b ∨ Raise b a :=
  (lt_or_gt_of_ne h.different).imp id id

-- ══════════════════════════════════════════════════════
-- 2. CONCEPTS GROUNDED IN CONTRAST-BASED SIMILARITY
--
--    A Koncept carries χ : α → Depth (one integer scale per concept).
--    Choosing which characteristic defines χ is the hard epistemological
--    problem — the formalization assumes it is solved externally.
--
--    Two typed wrappers make it explicit that both comparisons are
--    always relative to a characteristic, not floating raw numbers:
--      RaiseOn χ x y    — x strictly less deep than y under χ (level)
--      SimilarOn χ a b c — a and b similar contrasted with c under χ (gap)
--
--    CCD₃ axiomatizes (does not derive) contrast-grounded differentiation:
--    any two distinct units admit an external contrast witness.
--    CCDWitness₃ records one such witness as evidence (no global proof needed).
-- ══════════════════════════════════════════════════════

/-- Level comparison relative to a characteristic. -/
def RaiseOn {α : Type} (χ : Characteristic α) (x y : α) : Prop := Raise (χ x) (χ y)

/-- Ternary similarity relative to a characteristic. -/
def SimilarOn {α : Type} (χ : Characteristic α) (a b c : α) : Prop :=
  SimilarByContrast (χ a) (χ b) (χ c)

structure Koncept (α : Type) where
  pred : α → Prop
  χ    : Characteristic α   -- the characteristic's degree function

@[ext]
theorem Koncept.ext {α : Type} {k1 k2 : Koncept α}
    (hp : k1.pred = k2.pred) (hχ : k1.χ = k2.χ) : k1 = k2 := by
  cases k1; cases k2; simp_all

def Koncept.extension {α : Type} (k : Koncept α) : Set α := { a | k.pred a }

/-- CCD₃ axiomatizes contrast-grounded differentiation: for any two distinct units,
    there exists a contrast entity outside the concept such that the units are
    closer to each other (in χ) than either is to the contrast.
    This is a formal constraint on the concept, not a derived theorem. -/
def CCD₃ {α : Type} (k : Koncept α) : Prop :=
  ∀ ⦃a b⦄, k.pred a → k.pred b → a ≠ b →
    ∃ c, ¬k.pred c ∧ SimilarByContrast (k.χ a) (k.χ b) (k.χ c)

/-- CCDWitness₃: records a specific contrast-grounding for two units of a concept.
    Preferred over CCD₃ when you want to carry evidence through proofs
    rather than assert global existence. -/
structure CCDWitness₃ (α : Type) where
  k        : Koncept α
  a        : α
  b        : α
  contrast : α
  ha       : k.pred a
  hb       : k.pred b
  hc       : ¬k.pred contrast
  hab      : a ≠ b
  similar  : SimilarOn k.χ a b contrast

-- From a CCDWitness₃, the "different degree" conjunct of SimilarOn gives
-- a Raise in some direction between the two units (by linearity of ℤ).
-- The gap inequalities are not used here — only the a ≠ b conjunct.
theorem CCDWitness₃.hasRaise {α : Type} (w : CCDWitness₃ α) :
    Raise (w.k.χ w.a) (w.k.χ w.b) ∨ Raise (w.k.χ w.b) (w.k.χ w.a) :=
  w.similar.hasRaise

-- Commensurability is structural: units of the same concept share χ
theorem units_commensurable {α : Type} (k : Koncept α) (_a _b : α) :
    ∃ χ : Characteristic α, χ = k.χ := ⟨k.χ, rfl⟩

-- NOTE: this preorder is by EXTENSION only — it does not constrain χ at all.
-- This is a deliberate modeling choice: concept subsumption is about which
-- entities fall under the concept, not about their characteristic depths.
-- Consequence: `meet`/`join` define χ := max, but monotonicity facts about χ
-- do not follow from ≤. If you need "concept refinement preserves χ", you
-- would need a strengthened order that also requires χ compatibility.
instance {α : Type} : Preorder (Koncept α) where
  le c d               := ∀ a, c.pred a → d.pred a
  le_refl _            := fun _ ha => ha
  le_trans _ _ _ h1 h2 := fun a ha => h2 a (h1 a ha)

open Classical in
noncomputable def Koncept.meet {α : Type} (c d : Koncept α) : Koncept α :=
  { pred := fun a => c.pred a ∧ d.pred a
    χ    := fun a => max (c.χ a) (d.χ a) }

theorem meet_le_left {α : Type} (c d : Koncept α) : c.meet d ≤ c :=
  fun _ ha => ha.1

theorem meet_le_right {α : Type} (c d : Koncept α) : c.meet d ≤ d :=
  fun _ ha => ha.2

theorem meet_universal {α : Type} {c d e : Koncept α}
    (h1 : e ≤ c) (h2 : e ≤ d) : e ≤ c.meet d :=
  fun a ha => ⟨h1 a ha, h2 a ha⟩

open Classical in
noncomputable def Koncept.join {α : Type} (c d : Koncept α) : Koncept α :=
  { pred := fun a => c.pred a ∨ d.pred a
    χ    := fun a => max (c.χ a) (d.χ a) }

theorem le_join_left {α : Type} (c d : Koncept α) : c ≤ c.join d :=
  fun _a ha => Or.inl ha

theorem le_join_right {α : Type} (c d : Koncept α) : d ≤ c.join d :=
  fun _a ha => Or.inr ha

/-- Essential definition: differentia is strictly deeper (Raise) than genus
    for every unit. This is a LEVEL comparison, not a gap comparison. -/
structure KonceptDef (α : Type) where
  definiendum : Koncept α
  genus       : Koncept α
  differentia : Koncept α
  isMeet      : definiendum = genus.meet differentia
  isEssential : ∀ (a : α), definiendum.pred a →
                  Raise (genus.χ a) (differentia.χ a)
  -- Contrast-grounded CCD: a witness that two units of the definiendum
  -- are similar relative to something outside it that lacks the differentia.
  -- This grounds WHY the raise is essential, not just that it holds.
  -- Without this, isEssential could be satisfied by an arbitrary raise.
  ccd          : CCDWitness₃ α
  -- The witness is about the definiendum specifically
  ccd_concept  : ccd.k = definiendum
  -- The contrast entity lacks the differentia — it is what the units
  -- are differentiated FROM, not just something outside the definiendum
  ccd_contrast : ¬differentia.pred ccd.contrast

theorem definiendum_le_genus {α : Type} (d : KonceptDef α) :
    d.definiendum ≤ d.genus := d.isMeet ▸ meet_le_left _ _

theorem definiendum_le_differentia {α : Type} (d : KonceptDef α) :
    d.definiendum ≤ d.differentia := d.isMeet ▸ meet_le_right _ _

theorem definition_universal {α : Type} (d : KonceptDef α)
    (c : Koncept α) (hg : c ≤ d.genus) (hdiff : c ≤ d.differentia) :
    c ≤ d.definiendum := d.isMeet ▸ meet_universal hg hdiff

-- ══════════════════════════════════════════════════════
-- 3. KENNEDY — RHETORICAL AMPLIFICATION
--    Uses LEVEL comparison (Raise), not gap comparison.
-- ══════════════════════════════════════════════════════

inductive Canon : Type where
  | invention | style | arrangement
  deriving DecidableEq, Repr

inductive Dimension : Type where
  | vertical | horizontal
  deriving DecidableEq, Repr

inductive Mode : Type where
  | logical | pathetic | ethical | spiritual
  deriving DecidableEq, Repr

structure Comparison where
  baseline : Depth
  subject  : Depth
  holds    : baseline ≤ subject

structure AmplificationMove where
  comparison : Comparison
  canon      : Canon
  dimension  : Dimension
  mode       : Mode
  isStrict   : Raise comparison.baseline comparison.subject

def mkAuxesis (b s : Depth) (h : Raise b s) : AmplificationMove :=
  { comparison := ⟨b, s, le_of_lt h⟩
    canon      := .invention
    dimension  := .vertical
    mode       := .logical
    isStrict   := h }

def mkEmotional (b s : Depth) (h : Raise b s) : AmplificationMove :=
  { comparison := ⟨b, s, le_of_lt h⟩
    canon      := .invention
    dimension  := .vertical
    mode       := .pathetic
    isStrict   := h }

def mkEnergetic (b s : Depth) (h : Raise b s) : AmplificationMove :=
  { comparison := ⟨b, s, le_of_lt h⟩
    canon      := .style
    dimension  := .vertical
    mode       := .logical
    isStrict   := h }

def mkDilatatio (b s : Depth) (h : Raise b s) : AmplificationMove :=
  { comparison := ⟨b, s, le_of_lt h⟩
    canon      := .arrangement
    dimension  := .horizontal
    mode       := .logical
    isStrict   := h }

theorem kennedy_master_claim (m : AmplificationMove) :
    Raise m.comparison.baseline m.comparison.subject := m.isStrict

def AmplificationMove.compose
    (m1 m2 : AmplificationMove)
    (hlink  : m1.comparison.subject = m2.comparison.baseline)
    (_hdim  : m1.dimension = m2.dimension)
    (_hcan  : m1.canon = m2.canon)
    (_hmode : m1.mode = m2.mode) : AmplificationMove :=
  { comparison :=
      { baseline := m1.comparison.baseline
        subject  := m2.comparison.subject
        holds    := le_trans m1.comparison.holds (hlink ▸ m2.comparison.holds) }
    canon     := m1.canon
    dimension := m1.dimension
    mode      := m1.mode
    isStrict  := by
      show m1.comparison.baseline < m2.comparison.subject
      exact Int.lt_trans m1.isStrict (hlink ▸ m2.isStrict) }

-- ══════════════════════════════════════════════════════
-- 4. THE ABSTRACT SHARED STRUCTURE
--    SignificanceRaise = a named Raise with its proof carried along.
-- ══════════════════════════════════════════════════════

structure SignificanceRaise where
  baseline : Depth
  subject  : Depth
  isStrict : Raise baseline subject

def SignificanceRaise.compose (r1 r2 : SignificanceRaise)
    (hlink : r1.subject = r2.baseline) : SignificanceRaise :=
  { baseline := r1.baseline
    subject  := r2.subject
    isStrict := by
      show r1.baseline < r2.subject
      exact Int.lt_trans r1.isStrict (hlink ▸ r2.isStrict) }

-- ══════════════════════════════════════════════════════
-- 5. THE TWO EMBEDDINGS — BOTH TOTAL
-- ══════════════════════════════════════════════════════

def AmplificationMove.toSignificanceRaise (m : AmplificationMove) :
    SignificanceRaise :=
  { baseline := m.comparison.baseline
    subject  := m.comparison.subject
    isStrict := m.isStrict }

def KonceptDef.toSignificanceRaise {α : Type}
    (d : KonceptDef α) (a : α) (ha : d.definiendum.pred a) :
    SignificanceRaise :=
  { baseline := d.genus.χ a
    subject  := d.differentia.χ a
    isStrict := d.isEssential a ha }

-- ══════════════════════════════════════════════════════
-- 6. AMPLIFICATIONOVER AND ROUND-TRIP
-- ══════════════════════════════════════════════════════

structure AmplificationOver (α : Type) where
  definiendum  : Koncept α
  genus        : Koncept α
  differentia  : Koncept α
  isMeet       : definiendum = genus.meet differentia
  entity       : α
  inDef        : definiendum.pred entity
  move         : AmplificationMove
  baseline_ok  : move.comparison.baseline = genus.χ entity
  subject_ok   : move.comparison.subject  = differentia.χ entity
  isEssential  : ∀ (a : α), definiendum.pred a →
                   Raise (genus.χ a) (differentia.χ a)
  ccd          : CCDWitness₃ α
  ccd_concept  : ccd.k = definiendum
  ccd_contrast : ¬differentia.pred ccd.contrast

abbrev KonceptDefWithUnit (α : Type) :=
  Σ' d : KonceptDef α, Σ' a : α, d.definiendum.pred a

def toAmpOver {α : Type} (x : KonceptDefWithUnit α) : AmplificationOver α :=
  { definiendum  := x.1.definiendum
    genus        := x.1.genus
    differentia  := x.1.differentia
    isMeet       := x.1.isMeet
    entity       := x.2.1
    inDef        := x.2.2
    move         :=
      { comparison := ⟨x.1.genus.χ x.2.1, x.1.differentia.χ x.2.1,
                        le_of_lt (x.1.isEssential x.2.1 x.2.2)⟩
        canon      := .invention
        dimension  := .vertical
        mode       := .logical
        isStrict   := x.1.isEssential x.2.1 x.2.2 }
    baseline_ok  := rfl
    subject_ok   := rfl
    isEssential  := x.1.isEssential
    ccd          := x.1.ccd
    ccd_concept  := x.1.ccd_concept
    ccd_contrast := x.1.ccd_contrast }

def fromAmpOver {α : Type} (ao : AmplificationOver α) : KonceptDefWithUnit α :=
  ⟨{ definiendum  := ao.definiendum
     genus        := ao.genus
     differentia  := ao.differentia
     isMeet       := ao.isMeet
     isEssential  := ao.isEssential
     ccd          := ao.ccd
     ccd_concept  := ao.ccd_concept
     ccd_contrast := ao.ccd_contrast },
   ao.entity, ao.inDef⟩

theorem roundtrip_fwd {α : Type} (x : KonceptDefWithUnit α) :
    fromAmpOver (toAmpOver x) = x := by
  obtain ⟨d, a, ha⟩ := x; rfl

theorem roundtrip_bwd {α : Type} (ao : AmplificationOver α) :
    (toAmpOver (fromAmpOver ao)).definiendum  = ao.definiendum  ∧
    (toAmpOver (fromAmpOver ao)).genus        = ao.genus        ∧
    (toAmpOver (fromAmpOver ao)).differentia  = ao.differentia  ∧
    (toAmpOver (fromAmpOver ao)).entity       = ao.entity       ∧
    (toAmpOver (fromAmpOver ao)).isEssential  = ao.isEssential  ∧
    (toAmpOver (fromAmpOver ao)).ccd          = ao.ccd          ∧
    (toAmpOver (fromAmpOver ao)).ccd_concept  = ao.ccd_concept  ∧
    (toAmpOver (fromAmpOver ao)).ccd_contrast = ao.ccd_contrast :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ══════════════════════════════════════════════════════
-- 7. UNIFIED SIGNIFICANCE THEOREM
-- ══════════════════════════════════════════════════════

theorem unified_significance {α : Type} (ao : AmplificationOver α) :
    let amp_raise := ao.move.toSignificanceRaise
    let def_raise := (fromAmpOver ao).1.toSignificanceRaise ao.entity ao.inDef
    amp_raise.baseline = def_raise.baseline ∧
    amp_raise.subject  = def_raise.subject :=
  ⟨ao.baseline_ok, ao.subject_ok⟩

-- ══════════════════════════════════════════════════════
-- 8. EXAMPLE — DOGS, WOLVES, AND CATS
--    Gap comparison (contrast): dogs and wolves similar vs cats.
--    canine χ: dog=5, wolf=6, cat=2
--    Gap(5,6) = 1 < Gap(5,2) = 3  ✓
--    Gap(5,6) = 1 < Gap(6,2) = 4  ✓
-- ══════════════════════════════════════════════════════

inductive Mammal : Type where
  | dog | wolf | cat
  deriving DecidableEq, Repr

def canine : Characteristic Mammal
  | .dog  => 5
  | .wolf => 6
  | .cat  => 2

theorem dog_wolf_similar_to_cat :
    SimilarByContrast (canine .dog) (canine .wolf) (canine .cat) := by
  refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide

theorem dog_wolf_has_raise :
    Raise (canine .dog) (canine .wolf) ∨ Raise (canine .wolf) (canine .dog) :=
  dog_wolf_similar_to_cat.hasRaise

-- ══════════════════════════════════════════════════════
-- 9. EXAMPLE — "MAN = RATIONAL ANIMAL"
--    Level comparison (Raise): rationality deeper than animality.
-- ══════════════════════════════════════════════════════

-- LivingThing now has two rational animals (man, human) so konceptMan
-- has two distinct units, making the CCDWitness₃ constructible.
inductive LivingThing : Type where
  | man | human | dog | oak
  deriving DecidableEq, Repr

def konceptAnimal : Koncept LivingThing :=
  { pred := fun x => match x with
      | .man => True | .human => True | .dog => True | .oak => False
    χ    := fun x => match x with
      | .man => 1 | .human => 1 | .dog => 1 | .oak => 0 }

-- man and human differ in degree of rationality (3 vs 4)
-- so konceptMan has two units with different χ values
def konceptRational : Koncept LivingThing :=
  { pred := fun x => match x with
      | .man => True | .human => True | .dog => False | .oak => False
    χ    := fun x => match x with
      | .man => 3 | .human => 4 | .dog => 0 | .oak => 0 }

-- Defined concretely (not via noncomputable meet) so native_decide can evaluate it
def konceptMan : Koncept LivingThing :=
  { pred := fun x => match x with
      | .man => True | .human => True | .dog => False | .oak => False
    χ    := fun x => match x with
      | .man => 3 | .human => 4 | .dog => 1 | .oak => 0 }

-- The CCDWitness₃ for defMan:
-- man and human are similar as rational animals relative to dog
-- konceptMan.χ man   = max(1,3) = 3
-- konceptMan.χ human = max(1,4) = 4
-- konceptMan.χ dog   = max(1,0) = 1
-- Gap(3,4) = 1 < Gap(3,1) = 2  ✓
-- Gap(3,4) = 1 < Gap(4,1) = 3  ✓
-- dog lacks rationality (ccd_contrast: ¬konceptRational.pred .dog)
noncomputable def manCCDWitness : CCDWitness₃ LivingThing :=
  { k        := konceptMan
    a        := .man
    b        := .human
    contrast := .dog
    ha       := trivial
    hb       := trivial
    hc       := fun h => h      -- konceptMan.pred .dog = False
    hab      := by decide
    similar  := by
      refine ⟨by native_decide, ?_, ?_⟩ <;> native_decide }

noncomputable def defMan : KonceptDef LivingThing :=
  { definiendum  := konceptMan
    genus        := konceptAnimal
    differentia  := konceptRational
    isMeet       := by
      apply Koncept.ext
      · ext a; cases a <;> simp [konceptMan, konceptAnimal, konceptRational, Koncept.meet]
      · ext a; cases a <;> simp [konceptMan, konceptAnimal, konceptRational, Koncept.meet]
    isEssential  := by
      intro a ha
      cases a with
      | man   => show (1 : ℤ) < 3; omega
      | human => show (1 : ℤ) < 4; omega
      | dog   => exact ha.elim
      | oak   => exact ha.elim
    ccd          := manCCDWitness
    ccd_concept  := rfl
    ccd_contrast := fun h => h }

noncomputable def manUnit : KonceptDefWithUnit LivingThing :=
  ⟨defMan, .man, trivial⟩

noncomputable def manOver : AmplificationOver LivingThing := toAmpOver manUnit

noncomputable def manRaise : SignificanceRaise :=
  defMan.toSignificanceRaise .man trivial

theorem man_raise_levels : manRaise.baseline = 1 ∧ manRaise.subject = 3 :=
  ⟨rfl, rfl⟩

theorem roundtrip_man : fromAmpOver manOver = manUnit := roundtrip_fwd manUnit

-- ══════════════════════════════════════════════════════
-- 10. CICERO'S ARGUMENT CHAIN
--     Level comparison (Raise), chains transitively.
-- ══════════════════════════════════════════════════════

def cicero1 : SignificanceRaise :=
  { baseline := (2 : ℤ)
    subject  := (5 : ℤ)
    isStrict := by show (2 : ℤ) < 5; omega }

def cicero2 : SignificanceRaise :=
  { baseline := (5 : ℤ)
    subject  := (9 : ℤ)
    isStrict := by show (5 : ℤ) < 9; omega }

theorem cicero_link : cicero1.subject = cicero2.baseline := rfl

def ciceroChain : SignificanceRaise := cicero1.compose cicero2 cicero_link

theorem cicero_reaches_9 : ciceroChain.subject = 9 := rfl

theorem cicero_total_gap :
    Raise ciceroChain.baseline ciceroChain.subject :=
  ciceroChain.isStrict

-- ══════════════════════════════════════════════════════
-- 11. SYLLOGISTIC REASONING
--
--    Classical syllogistic has four figures and multiple moods.
--    We formalize the three most fundamental:
--
--    Barbara (AAA-1): All M are P. All S are M. ∴ All S are P.
--    Celarent (EAE-1): No M are P. All S are M. ∴ No S are P.
--    Darii (AII-1): All M are P. Some S are M. ∴ Some S are P.
--
--    In concept-preorder terms:
--      "All M are P"  =  M ≤ P  (every unit of M is a unit of P)
--      "No M are P"   =  M and P have disjoint extensions
--      "Some S are M" =  ∃ a, S.pred a ∧ M.pred a  (a witness)
--      "Some S are P" =  ∃ a, S.pred a ∧ P.pred a
--
--    The conclusions are THEOREMS, not axioms — they follow necessarily
--    from the premises. This is what makes a syllogism valid.
--
--    Connection to KonceptDef: definiendum_le_genus and
--    definiendum_le_differentia are both instances of Barbara —
--    every unit of the defined concept falls under the genus/differentia.
--    A good definition licenses valid syllogistic inference.
-- ══════════════════════════════════════════════════════

/-- Barbara (AAA-1): All M are P. All S are M. Therefore all S are P.
    The universal affirmative syllogism — transitivity of the concept preorder. -/
structure Barbara (α : Type) where
  S          : Koncept α   -- subject concept
  M          : Koncept α   -- middle concept
  P          : Koncept α   -- predicate concept
  allMareP   : M ≤ P       -- major premise: all M are P
  allSareM   : S ≤ M       -- minor premise: all S are M

/-- The conclusion of Barbara: all S are P. Proved, not assumed. -/
theorem Barbara.conclusion {α : Type} (b : Barbara α) : b.S ≤ b.P :=
  le_trans b.allSareM b.allMareP

/-- Celarent (EAE-1): No M are P. All S are M. Therefore no S are P.
    The universal negative syllogism. -/
structure Celarent (α : Type) where
  S          : Koncept α
  M          : Koncept α
  P          : Koncept α
  noMareP    : ∀ a, M.pred a → ¬P.pred a   -- major premise: no M are P
  allSareM   : S ≤ M                        -- minor premise: all S are M

theorem Celarent.conclusion {α : Type} (c : Celarent α) :
    ∀ a, c.S.pred a → ¬c.P.pred a :=
  fun a ha => c.noMareP a (c.allSareM a ha)

/-- Darii (AII-1): All M are P. Some S are M. Therefore some S are P.
    The particular affirmative syllogism — existence passes through the preorder. -/
structure Darii (α : Type) where
  S          : Koncept α
  M          : Koncept α
  P          : Koncept α
  allMareP   : M ≤ P                        -- major premise: all M are P
  someSareM  : ∃ a, S.pred a ∧ M.pred a    -- minor premise: some S are M

theorem Darii.conclusion {α : Type} (d : Darii α) :
    ∃ a, d.S.pred a ∧ d.P.pred a := by
  obtain ⟨a, hS, hM⟩ := d.someSareM
  exact ⟨a, hS, d.allMareP a hM⟩

-- ══════════════════════════════════════════════════════
-- 12. SYLLOGISMS FROM ESSENTIAL DEFINITIONS
--
--    definiendum_le_genus and definiendum_le_differentia are Barbara.
--    Any KonceptDef licenses two immediate Barbara syllogisms.
--    The connection between definition and inference is structural.
-- ══════════════════════════════════════════════════════

/-- Every essential definition licenses a Barbara syllogism to the genus.
    "All men are animals" follows from the definition of Man. -/
def KonceptDef.barbaraToGenus {α : Type} (d : KonceptDef α) : Barbara α :=
  { S        := d.definiendum
    M        := d.definiendum
    P        := d.genus
    allMareP := definiendum_le_genus d
    allSareM := le_refl _ }

/-- Every essential definition licenses a Barbara syllogism to the differentia.
    "All men are rational" follows from the definition of Man. -/
def KonceptDef.barbaraToDifferentia {α : Type} (d : KonceptDef α) : Barbara α :=
  { S        := d.definiendum
    M        := d.definiendum
    P        := d.differentia
    allMareP := definiendum_le_differentia d
    allSareM := le_refl _ }

/-- From the CCD witness, a Darii syllogism:
    Some units of the definiendum are similar to each other (witnessed). -/
def KonceptDef.darii {α : Type} (d : KonceptDef α) : Darii α :=
  { S        := d.definiendum
    M        := d.definiendum
    P        := d.definiendum
    allMareP := le_refl _
    someSareM := ⟨d.ccd.a, d.ccd_concept ▸ d.ccd.ha, d.ccd_concept ▸ d.ccd.ha⟩ }

-- ══════════════════════════════════════════════════════
-- 13. CONCRETE SYLLOGISMS — MAN, ANIMAL, RATIONAL
-- ══════════════════════════════════════════════════════

/-- All men are animals — Barbara from the definition of Man. -/
noncomputable def manIsAnimal : Barbara LivingThing :=
  defMan.barbaraToGenus

theorem all_men_are_animals :
    ∀ a, konceptMan.pred a → konceptAnimal.pred a :=
  manIsAnimal.conclusion

/-- All men are rational — Barbara from the definition of Man. -/
noncomputable def manIsRational : Barbara LivingThing :=
  defMan.barbaraToDifferentia

theorem all_men_are_rational :
    ∀ a, konceptMan.pred a → konceptRational.pred a :=
  manIsRational.conclusion

/-- No rational beings are dogs — Celarent example. -/
def rationalNotDog : Celarent LivingThing :=
  { S       := konceptRational
    M       := konceptRational
    P       := { pred := fun x => match x with | .dog => True | _ => False
                 χ    := fun _ => 0 }
    noMareP := fun a ha hpa =>
      match a, ha, hpa with
      | .man,   _, hpa => hpa
      | .human, _, hpa => hpa
    allSareM := le_refl _ }

/-- Some men exist — Darii from the CCD witness (man, human are both units). -/
noncomputable def someMenExist : Darii LivingThing :=
  defMan.darii

theorem some_men_exist :
    ∃ a, konceptMan.pred a ∧ konceptMan.pred a :=
  someMenExist.conclusion
