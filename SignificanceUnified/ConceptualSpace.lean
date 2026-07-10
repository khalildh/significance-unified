import Basic
import Consequences
import Mathlib.Data.Fin.VecNotation

/-!
# Multi-Dimensional Conceptual Spaces

`Basic.lean` puts every characteristic on a single integer scale `χ : α → ℤ`.
Gärdenfors's *conceptual spaces* suggest the honest setting is
multi-dimensional: entities live at points in a space of quality dimensions,
similarity is distance in that space, and concepts are regions that cluster
under contrast.

This file generalizes the depth scale from `ℤ` to `Point n := Fin n → ℤ`
(L1 metric) and asks, for every theorem in the 1-D theory: **does it survive,
or was it an artifact of dimension one?**

## The partition

Survives in every dimension (structural results):
* translation invariance of gap and similarity   (`dist₁_translate`)
* symmetry of similarity, distinguished contrast (`SimilarByContrastN.symm`)
* irreversibility of raises                      (`RaiseProd.irreversible`)
* acyclicity / no definition cycles              (`no_definition_cycleN`)
* the minimum quantum of significance            (`raiseProd_min_quantum`)
* genus ≠ differentia, two-unit minimum          (`genus_ne_differentiaN`, …)

Dies above dimension one (ℤ-artifacts):
* **direction from difference** — in 1-D, `a ≠ b` forces `Raise a b ∨ Raise b a`
  by linearity of ℤ. In dimension ≥ 2 the product order is not total:
  two entities can differ without either being deeper
  (`similar_without_raise_dim2`). The 1-D `hasRaise` was load-bearing
  linearity, not conceptual structure.

Recovered by choice of weights:
* any positive linear functional `DepthFunctional` collapses the space back
  to the 1-D theory (`DepthFunctional.mono`) — the original formalization is
  the image of the multi-D theory under a choice of weights. But different
  weightings disagree about direction on incomparable pairs
  (`functionals_disagree`): in a conceptual space, *which* of two concepts is
  "deeper" is imposed by a weighting, not discovered in the geometry.
-/

-- ══════════════════════════════════════════════════════
-- 1. POINTS AND THE L1 METRIC
-- ══════════════════════════════════════════════════════

/-- A point in an `n`-dimensional conceptual space: one integer coordinate
    per quality dimension. `Point 1` recovers the original `Depth` scale. -/
abbrev Point (n : ℕ) := Fin n → ℤ

/-- A multi-dimensional characteristic: each entity sits at a point. -/
abbrev CharacteristicN (n : ℕ) (α : Type) := α → Point n

/-- L1 (taxicab) distance between two points, as ℕ.
    Chosen over L2 to stay in decidable territory (`decide` closes
    concrete goals), exactly as `Gap` chose ℤ over ℝ. -/
def dist₁ {n : ℕ} (a b : Point n) : ℕ := ∑ i, (a i - b i).natAbs

theorem dist₁_symm {n : ℕ} (a b : Point n) : dist₁ a b = dist₁ b a :=
  Finset.sum_congr rfl fun i _ => by omega

theorem dist₁_self {n : ℕ} (a : Point n) : dist₁ a a = 0 := by
  simp [dist₁]

/-- The metric is definite: zero distance iff the same point.
    Generalizes `Gap.eq_zero_iff`. -/
theorem dist₁_eq_zero_iff {n : ℕ} {a b : Point n} :
    dist₁ a b = 0 ↔ a = b := by
  rw [dist₁, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    omega
  · rintro rfl i _
    simp

/-- Gap is translation-invariant in every dimension: the origin of a
    conceptual space is conventional. Generalizes `Gap.translate`. -/
theorem dist₁_translate {n : ℕ} (a b t : Point n) :
    dist₁ (a + t) (b + t) = dist₁ a b :=
  Finset.sum_congr rfl fun i _ => by
    simp [Pi.add_apply, add_sub_add_right_eq_sub]

/-- In dimension 1, `dist₁` is exactly the original `Gap`. -/
theorem dist₁_one (a b : Point 1) : dist₁ a b = Gap (a 0) (b 0) := by
  simp [dist₁, Gap]

-- ══════════════════════════════════════════════════════
-- 2. GAP COMPARISON: SIMILARITY BY CONTRAST
-- ══════════════════════════════════════════════════════

/-- Ternary similarity in a conceptual space: `a` and `b` are similar as
    contrasted with `c`. Same three conjuncts as the 1-D
    `SimilarByContrast`, with L1 distance in place of `Gap`. -/
def SimilarByContrastN {n : ℕ} (a b c : Point n) : Prop :=
  a ≠ b ∧ dist₁ a b < dist₁ a c ∧ dist₁ a b < dist₁ b c

instance {n : ℕ} (a b c : Point n) : Decidable (SimilarByContrastN a b c) := by
  unfold SimilarByContrastN; infer_instance

instance (a b : Depth) : Decidable (Raise a b) := by
  unfold Raise; infer_instance

theorem SimilarByContrastN.symm {n : ℕ} {a b c : Point n}
    (h : SimilarByContrastN a b c) : SimilarByContrastN b a c := by
  obtain ⟨hne, h1, h2⟩ := h
  exact ⟨hne.symm, by rwa [dist₁_symm b a], by rwa [dist₁_symm b a]⟩

theorem SimilarByContrastN.contrastDiffers_a {n : ℕ} {a b c : Point n}
    (h : SimilarByContrastN a b c) : a ≠ c := by
  rintro rfl
  have := h.2.1
  simp [dist₁_self] at this

theorem SimilarByContrastN.contrastDiffers_b {n : ℕ} {a b c : Point n}
    (h : SimilarByContrastN a b c) : b ≠ c := by
  rintro rfl
  have := h.2.2
  simp [dist₁_self] at this

/-- The contrast position remains structurally distinguished in every
    dimension: the symmetry group is S₂, not S₃.
    Generalizes `contrast_not_interchangeable`. -/
theorem similarN_not_interchangeable :
    ∃ (a b c : Point 2), SimilarByContrastN a b c ∧ ¬SimilarByContrastN a c b :=
  ⟨![0, 0], ![1, 0], ![5, 5], by decide, by decide⟩

/-- Similarity is translation-invariant in every dimension.
    Generalizes `SimilarByContrast.translate`. -/
theorem SimilarByContrastN.translate {n : ℕ} {a b c : Point n}
    (t : Point n) (h : SimilarByContrastN a b c) :
    SimilarByContrastN (a + t) (b + t) (c + t) := by
  obtain ⟨hne, h1, h2⟩ := h
  refine ⟨fun heq => hne ?_, ?_, ?_⟩
  · funext i
    have := congrFun heq i
    simp [Pi.add_apply] at this
    omega
  · rwa [dist₁_translate, dist₁_translate]
  · rwa [dist₁_translate, dist₁_translate]

-- ══════════════════════════════════════════════════════
-- 3. LEVEL COMPARISON: THE PRODUCT ORDER RAISE
--
--    In 1-D, Raise a b := a < b on ℤ (a total order).
--    In n dimensions the honest generalization is the strict
--    PRODUCT order: deeper on every dimension, strictly on one.
--    This is a partial order — and that partiality is the
--    philosophical payload of the generalization.
-- ══════════════════════════════════════════════════════

/-- Level comparison in a conceptual space: `b` is at least as deep as `a`
    on every quality dimension, and strictly deeper on at least one
    (equivalently: dominance plus inequality). -/
def RaiseProd {n : ℕ} (a b : Point n) : Prop :=
  (∀ i, a i ≤ b i) ∧ a ≠ b

instance {n : ℕ} (a b : Point n) : Decidable (RaiseProd a b) := by
  unfold RaiseProd; infer_instance

/-- `RaiseProd` is the strict order of the product (pointwise) order. -/
theorem raiseProd_iff_lt {n : ℕ} {a b : Point n} :
    RaiseProd a b ↔ a < b := by
  rw [lt_iff_le_and_ne]
  exact and_congr_left' (by rfl)

theorem RaiseProd.trans {n : ℕ} {a b c : Point n}
    (h1 : RaiseProd a b) (h2 : RaiseProd b c) : RaiseProd a c := by
  rw [raiseProd_iff_lt] at *
  exact lt_trans h1 h2

theorem RaiseProd.irrefl {n : ℕ} (a : Point n) : ¬RaiseProd a a :=
  fun h => h.2 rfl

/-- Amplification is irreversible in every dimension.
    Generalizes `AmplificationMove.irreversible` — survives. -/
theorem RaiseProd.irreversible {n : ℕ} {a b : Point n}
    (h : RaiseProd a b) : ¬RaiseProd b a := fun h' =>
  h.2 (funext fun i => le_antisymm (h.1 i) (h'.1 i))

/-- No cycles in any dimension. The 1-D `no_definition_cycle` was not an
    artifact of ℤ's linearity — any strict order forbids cycles. Survives. -/
theorem raiseProd_no_cycle {n : ℕ} {a b c : Point n}
    (h1 : RaiseProd a b) (h2 : RaiseProd b c) (h3 : RaiseProd c a) : False :=
  RaiseProd.irrefl a ((h1.trans h2).trans h3)

/-- The minimum quantum of significance survives: every raise moves the
    point by L1 distance at least 1. Generalizes `amplification_min_quantum`. -/
theorem raiseProd_min_quantum {n : ℕ} {a b : Point n}
    (h : RaiseProd a b) : 1 ≤ dist₁ a b := by
  rcases Nat.eq_zero_or_pos (dist₁ a b) with h0 | h1
  · exact absurd (dist₁_eq_zero_iff.mp h0) h.2
  · exact h1

-- ══════════════════════════════════════════════════════
-- 4. WHAT DIES: DIRECTION FROM DIFFERENCE
--
--    The 1-D theorem SimilarByContrast.hasRaise says: from a ≠ b,
--    a Raise follows in SOME direction. Its proof is linearity of ℤ.
--    In dimension ≥ 2 the product order is not total, and the theorem
--    is FALSE: a contrast witness can ground similarity between two
--    entities neither of which is deeper than the other.
-- ══════════════════════════════════════════════════════

/-- **The 1-D `hasRaise` is a dimension artifact.** In `Point 2` there is a
    contrast-grounded similarity between two points that are incomparable
    in the product order: `(0,1)` and `(1,0)` are similar as contrasted
    with `(5,5)`, yet neither is deeper than the other. Contrast grounds
    *grouping*; it cannot ground *direction* once space has two dimensions. -/
theorem similar_without_raise_dim2 :
    ∃ (a b c : Point 2), SimilarByContrastN a b c ∧
      ¬RaiseProd a b ∧ ¬RaiseProd b a :=
  ⟨![0, 1], ![1, 0], ![5, 5], by decide, by decide, by decide⟩

/-- In dimension 1 the direction theorem is recovered: difference forces a
    raise in some direction, exactly as in `SimilarByContrast.hasRaise`.
    Totality of ℤ's order is what the 1-D theory was silently using. -/
theorem hasRaise_dim_one {a b c : Point 1}
    (h : SimilarByContrastN a b c) : RaiseProd a b ∨ RaiseProd b a := by
  have hne : a 0 ≠ b 0 := by
    intro heq
    exact h.1 (funext fun i => by rw [Fin.eq_zero i]; exact heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ⟨fun i => by rw [Fin.eq_zero i]; exact le_of_lt hlt, h.1⟩
  · exact Or.inr ⟨fun i => by rw [Fin.eq_zero i]; exact le_of_lt hgt,
      h.1 ∘ Eq.symm⟩

/-- Dimension-1 round trip: `RaiseProd` on `Point 1` is exactly `Raise`. -/
theorem raiseProd_one_iff {a b : Point 1} :
    RaiseProd a b ↔ Raise (a 0) (b 0) := by
  constructor
  · intro ⟨hle, hne⟩
    rcases lt_or_eq_of_le (hle 0) with h | h
    · exact h
    · exact absurd (funext fun i => by rw [Fin.eq_zero i]; exact h) hne
  · intro h
    exact ⟨fun i => by rw [Fin.eq_zero i]; exact le_of_lt h,
      fun heq => by simp [heq, Raise] at h⟩

-- ══════════════════════════════════════════════════════
-- 5. DEPTH FUNCTIONALS: RECOVERING THE 1-D THEORY
--
--    A positive weighting of the quality dimensions collapses the
--    space to a single scale. Every raise in the space becomes a
--    Raise on that scale — the original theory is the image of this
--    one under any choice of weights. But the choice is genuinely
--    extra structure: different weightings disagree about direction
--    on incomparable pairs.
-- ══════════════════════════════════════════════════════

/-- A positive linear functional on a conceptual space: a weighting of the
    quality dimensions. This is the "significance perspective" that turns
    a multi-dimensional position into a single depth. -/
structure DepthFunctional (n : ℕ) where
  w   : Fin n → ℤ
  pos : ∀ i, 0 < w i

/-- Evaluate the functional: weighted total depth of a point. -/
def DepthFunctional.eval {n : ℕ} (φ : DepthFunctional n) (a : Point n) : Depth :=
  ∑ i, φ.w i * a i

/-- Every depth functional is strictly monotone: a raise in the space is a
    `Raise` on the collapsed scale. The whole 1-D theory (transitivity,
    Cicero chains, essential definitions) applies to the image. -/
theorem DepthFunctional.mono {n : ℕ} (φ : DepthFunctional n)
    {a b : Point n} (h : RaiseProd a b) : Raise (φ.eval a) (φ.eval b) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp h.2
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  · exact mul_le_mul_of_nonneg_left (h.1 i) (le_of_lt (φ.pos i))
  · exact mul_lt_mul_of_pos_left (lt_of_le_of_ne (h.1 i₀) hi₀) (φ.pos i₀)

/-- **Direction is imposed, not discovered.** Two positive weightings can
    disagree about which of two (incomparable) points is deeper. On the
    pair `(0,1)` vs `(1,0)`: weights `(2,1)` say the first is deeper;
    weights `(1,2)` say the second is. The 1-D theory's confident
    directionality was a property of the chosen collapse, not of the
    conceptual space. -/
theorem functionals_disagree :
    ∃ (φ ψ : DepthFunctional 2) (a b : Point 2),
      Raise (φ.eval a) (φ.eval b) ∧ Raise (ψ.eval b) (ψ.eval a) :=
  ⟨⟨![2, 1], by decide⟩, ⟨![1, 2], by decide⟩, ![0, 1], ![1, 0],
    by decide, by decide⟩

-- ══════════════════════════════════════════════════════
-- 6. CONCEPTS IN CONCEPTUAL SPACES
-- ══════════════════════════════════════════════════════

/-- A concept over an `n`-dimensional conceptual space: a predicate plus a
    placement of every entity at a point. Generalizes `Koncept`. -/
structure KonceptN (n : ℕ) (α : Type) where
  pred : α → Prop
  χ    : CharacteristicN n α

def KonceptN.extension {n : ℕ} {α : Type} (k : KonceptN n α) : Set α :=
  { a | k.pred a }

/-- Concepts over a space are preordered by extension, exactly as in 1-D:
    the subsumption order never looked at χ, so it generalizes untouched. -/
instance {n : ℕ} {α : Type} : Preorder (KonceptN n α) where
  le c d               := ∀ a, c.pred a → d.pred a
  le_refl _            := fun _ ha => ha
  le_trans _ _ _ h1 h2 := fun a ha => h2 a (h1 a ha)

/-- Contrast-grounded differentiation in a conceptual space: any two
    distinct units admit an external contrast entity they are both closer
    to each other than to. Generalizes `CCD₃` — now a genuine
    *clusterability* condition on the concept's region. -/
def CCD₃N {n : ℕ} {α : Type} (k : KonceptN n α) : Prop :=
  ∀ ⦃a b⦄, k.pred a → k.pred b → a ≠ b →
    ∃ c, ¬k.pred c ∧ SimilarByContrastN (k.χ a) (k.χ b) (k.χ c)

/-- A recorded contrast witness in a conceptual space.
    Generalizes `CCDWitness₃`. -/
structure CCDWitness₃N (n : ℕ) (α : Type) where
  k        : KonceptN n α
  a        : α
  b        : α
  contrast : α
  ha       : k.pred a
  hb       : k.pred b
  hc       : ¬k.pred contrast
  hab      : a ≠ b
  similar  : SimilarByContrastN (k.χ a) (k.χ b) (k.χ contrast)

/-- Meet of concepts over the same space: conjunction of predicates,
    componentwise max of placements. -/
def KonceptN.meet {n : ℕ} {α : Type} (c d : KonceptN n α) : KonceptN n α where
  pred := fun a => c.pred a ∧ d.pred a
  χ    := fun a i => max (c.χ a i) (d.χ a i)

theorem KonceptN.meet_le_left {n : ℕ} {α : Type} (c d : KonceptN n α) :
    c.meet d ≤ c := fun _ ha => ha.1

theorem KonceptN.meet_le_right {n : ℕ} {α : Type} (c d : KonceptN n α) :
    c.meet d ≤ d := fun _ ha => ha.2

/-- Essential definition over a conceptual space. The essentiality raise is
    now the product order: the differentia must be deeper than the genus on
    EVERY quality dimension. This is a strictly stronger demand than any
    single-scale raise — multi-D essentiality does not come cheap. -/
structure KonceptDefN (n : ℕ) (α : Type) where
  definiendum : KonceptN n α
  genus       : KonceptN n α
  differentia : KonceptN n α
  isMeet      : definiendum = genus.meet differentia
  isEssential : ∀ (a : α), definiendum.pred a →
                  RaiseProd (genus.χ a) (differentia.χ a)
  ccd          : CCDWitness₃N n α
  ccd_concept  : ccd.k = definiendum
  ccd_contrast : ¬differentia.pred ccd.contrast

/-- Genus and differentia stay distinct in every dimension: equality would
    require `RaiseProd x x`. Generalizes `KonceptDef.genus_ne_differentia`
    — survives. -/
theorem KonceptDefN.genus_ne_differentia {n : ℕ} {α : Type}
    (d : KonceptDefN n α) (a : α) (ha : d.definiendum.pred a) :
    d.genus ≠ d.differentia := by
  intro heq
  exact RaiseProd.irrefl _ (heq ▸ d.isEssential a ha)

/-- Essential definitions still require two distinct units.
    Generalizes `KonceptDef.has_two_units` — survives. -/
theorem KonceptDefN.has_two_units {n : ℕ} {α : Type} (d : KonceptDefN n α) :
    ∃ a b, d.definiendum.pred a ∧ d.definiendum.pred b ∧ a ≠ b :=
  ⟨d.ccd.a, d.ccd.b, d.ccd_concept ▸ d.ccd.ha, d.ccd_concept ▸ d.ccd.hb,
    d.ccd.hab⟩

/-- Definition cycles remain impossible in every dimension. If A's
    differentia depth feeds B's genus and so on around a loop, the
    composed `RaiseProd` contradicts irreflexivity.
    Generalizes `no_definition_cycle` — survives. -/
theorem no_definition_cycleN {n : ℕ} {α : Type}
    (d1 d2 d3 : KonceptDefN n α) (a : α)
    (h1 : d1.definiendum.pred a) (h2 : d2.definiendum.pred a)
    (h3 : d3.definiendum.pred a)
    (link12 : d2.genus.χ a = d1.differentia.χ a)
    (link23 : d3.genus.χ a = d2.differentia.χ a)
    (link31 : d1.genus.χ a = d3.differentia.χ a) : False := by
  have r1 := d1.isEssential a h1
  have r2 := d2.isEssential a h2
  have r3 := d3.isEssential a h3
  rw [link12] at r2
  rw [link23] at r3
  rw [link31] at r1
  exact raiseProd_no_cycle r1 r2 r3

-- ══════════════════════════════════════════════════════
-- 7. WHAT DIES, AT THE CONCEPT LEVEL
--
--    CCDWitness₃.hasRaise (1-D): every contrast witness yields a
--    Raise between the two units in some direction. In dimension 2
--    this FAILS: a concept can be perfectly contrast-grounded while
--    its units are incomparable in depth.
-- ══════════════════════════════════════════════════════

inductive Critter | fox | hen | rock
  deriving DecidableEq

/-- A two-dimensional concept: foxes and hens are both "beasts", placed at
    incomparable points `(0,1)` and `(1,0)`; the rock sits far away at
    `(5,5)` and grounds the contrast. -/
def kBeast : KonceptN 2 Critter where
  pred := fun a => a ≠ .rock
  χ    := fun a => match a with
    | .fox  => ![0, 1]
    | .hen  => ![1, 0]
    | .rock => ![5, 5]

def beastWitness : CCDWitness₃N 2 Critter where
  k        := kBeast
  a        := .fox
  b        := .hen
  contrast := .rock
  ha       := by show Critter.fox ≠ Critter.rock; decide
  hb       := by show Critter.hen ≠ Critter.rock; decide
  hc       := by show ¬(Critter.rock ≠ Critter.rock); decide
  hab      := by decide
  similar  := by show SimilarByContrastN ![0, 1] ![1, 0] ![5, 5]; decide

/-- **Contrast without direction.** `beastWitness` is a fully valid CCD
    witness, yet neither unit is deeper than the other: the 1-D theorem
    `CCDWitness₃.hasRaise` does not generalize. In a conceptual space,
    grouping (which the witness provides) and direction (which `isEssential`
    demands) come apart — the choice of genus vs differentia is *pure*
    extra structure, not extractable from contrast even in principle. -/
theorem witness_hasRaise_fails :
    ¬RaiseProd (beastWitness.k.χ beastWitness.a) (beastWitness.k.χ beastWitness.b) ∧
    ¬RaiseProd (beastWitness.k.χ beastWitness.b) (beastWitness.k.χ beastWitness.a) :=
  ⟨by show ¬RaiseProd ![0, 1] ![1, 0]; decide,
   by show ¬RaiseProd ![1, 0] ![0, 1]; decide⟩
