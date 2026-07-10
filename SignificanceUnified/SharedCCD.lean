import ContrastScale

/-!
# The Shared CCD: Commensurate Essentiality

Two loose ends from `ContrastScale.lean`, tied off.

## 1. Only the ray matters (rescaling invariance)

The pipeline normalizes each concept's diagnostic weighting to a common
total attention before comparing scales. The Lean theorems so far were about
the *raw* weights, leaving a gap between what is formalized and what ships.
This file closes it: every audit predicate on a single weighted scale —
similarity, raise, distance comparisons — is **invariant under uniform
positive rescaling of the weighting** (`similarByContrastN_smul_iff`,
`raiseProd_smul_iff`). A weighting is only ever meaningful as a ray;
any common-total representative is as good as any other.

And the converse, which is the incommensurability finding made formal:
**independent** rescaling of one side flips cross-scale raise verdicts
(`raise_flips_under_independent_rescale`). A raise between two *different*
weightings is not invariant under the transformations each weighting is
defined up to — it is measurement-theoretically meaningless — unless the
weightings are tied to a common unit. That is what "conceptual COMMON
denominator" means, as a theorem.

## 2. `KonceptDefCCD`: essential definitions on a shared CCD

Rand's requirement is that genus and differentia be measured on a common
scale. `KonceptDefCCD` strengthens `KonceptDefN` accordingly: it carries a
shared entity placement `pos`, two attention profiles `wG`, `wD` with equal
total attention (`commensurate`), and proofs that the genus and differentia
characteristics ARE the weighted placements. Under that structure the
essentiality raise is invariant under change of the common unit
(`KonceptDefCCD.essential_rescale`) — commensuration is exactly what makes
essentiality meaningful. Every `KonceptDefCCD` forgets to a `KonceptDefN`
(`toKonceptDefN`), so all downstream theorems (two units, no cycles, …)
apply unchanged.
-/

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

-- ══════════════════════════════════════════════════════
-- 1. RESCALING A SCALE: ONLY THE RAY MATTERS
-- ══════════════════════════════════════════════════════

/-- Rescale a point by a constant (change of unit on every dimension). -/
def Point.smul (c : ℤ) (x : Point n) : Point n := fun i => c * x i

/-- L1 distance scales with the unit. -/
theorem dist₁_smul (c : ℤ) (x y : Point n) :
    dist₁ (Point.smul c x) (Point.smul c y) = c.natAbs * dist₁ x y := by
  unfold dist₁ Point.smul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.natAbs_mul]
  congr 1
  ring

theorem Point.smul_inj {c : ℤ} (hc : c ≠ 0) {x y : Point n}
    (h : Point.smul c x = Point.smul c y) : x = y := by
  funext i
  exact mul_left_cancel₀ hc (congrFun h i)

/-- **Similarity sees only the ray.** Similarity-by-contrast judgments are
    invariant under uniform positive rescaling of the scale: the pipeline's
    common-total normalization changes no CCD verdict. -/
theorem similarByContrastN_smul_iff {c : ℤ} (hc : 0 < c) (x y z : Point n) :
    SimilarByContrastN (Point.smul c x) (Point.smul c y) (Point.smul c z)
      ↔ SimilarByContrastN x y z := by
  unfold SimilarByContrastN
  have habs : 0 < c.natAbs := Int.natAbs_pos.mpr (ne_of_gt hc)
  rw [dist₁_smul, dist₁_smul, dist₁_smul,
    Nat.mul_lt_mul_left habs, Nat.mul_lt_mul_left habs]
  constructor
  · rintro ⟨hne, h1, h2⟩
    exact ⟨fun h => hne (h ▸ rfl), h1, h2⟩
  · rintro ⟨hne, h1, h2⟩
    exact ⟨fun h => hne (Point.smul_inj (ne_of_gt hc) h), h1, h2⟩

/-- **Raises on a single scale see only the ray.** -/
theorem raiseProd_smul_iff {c : ℤ} (hc : 0 < c) (x y : Point n) :
    RaiseProd (Point.smul c x) (Point.smul c y) ↔ RaiseProd x y := by
  unfold RaiseProd Point.smul
  constructor
  · rintro ⟨hle, hne⟩
    refine ⟨fun i => le_of_mul_le_mul_left (hle i) hc, fun h => hne ?_⟩
    funext i; rw [congrFun h i]
  · rintro ⟨hle, hne⟩
    refine ⟨fun i => mul_le_mul_of_nonneg_left (hle i) (le_of_lt hc),
      fun h => hne (Point.smul_inj (ne_of_gt hc) h)⟩

/-- **Cross-scale raises are meaningless without commensuration.** A raise
    between values on two DIFFERENT weightings flips when one weighting is
    rescaled — an admissible transformation if the scales are independent.
    Essentiality across independent scales is not a fact about the entities;
    it is an artifact of the units. (The incommensurability finding of the
    audit pipeline, as a theorem.) -/
theorem raise_flips_under_independent_rescale :
    ∃ (x y : Point 1) (c : ℤ), 0 < c ∧
      RaiseProd x y ∧ ¬RaiseProd (Point.smul c x) y :=
  ⟨(fun _ => 2), (fun _ => 3), 2, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════
-- 2. ESSENTIAL DEFINITIONS ON A SHARED CCD
-- ══════════════════════════════════════════════════════

/-- A weighted placement: entity position measured under an attention
    profile. This is `contrastChiIn` abstracted over where the weights
    came from. -/
def weightedChi (w : Fin n → ℕ) (pos : α → Point n) : α → Point n :=
  fun a i => (w i : ℤ) * pos a i

/-- An essential definition whose genus and differentia are measured on a
    **shared conceptual common denominator**: one entity placement `pos`,
    two attention profiles with equal total attention, and proofs that the
    two characteristics are exactly the weighted placements. This is the
    commensurability precondition that bare `KonceptDefN` lacks — Rand's
    "common denominator," as structure. -/
structure KonceptDefCCD (n : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  definiendum : KonceptN n α
  genus       : KonceptN n α
  differentia : KonceptN n α
  isMeet      : definiendum = genus.meet differentia
  /-- the shared placement: the CCD's quality dimensions -/
  pos         : α → Point n
  /-- attention profile of the genus characteristic -/
  wG          : Fin n → ℕ
  /-- attention profile of the differentia characteristic -/
  wD          : Fin n → ℕ
  /-- equal total attention: the two profiles share a unit -/
  commensurate : ∑ i, wG i = ∑ i, wD i
  /-- the genus characteristic IS the wG-weighted placement -/
  genusScale  : genus.χ = weightedChi wG pos
  /-- the differentia characteristic IS the wD-weighted placement -/
  diffScale   : differentia.χ = weightedChi wD pos
  isEssential : ∀ (a : α), definiendum.pred a →
                  RaiseProd (genus.χ a) (differentia.χ a)
  ccd          : CCDWitness₃N n α
  ccd_concept  : ccd.k = definiendum
  ccd_contrast : ¬differentia.pred ccd.contrast

/-- Every shared-CCD definition is in particular a `KonceptDefN`: the
    revision strengthens the spec, it does not fork it. All downstream
    theorems (`has_two_units`, `no_definition_cycleN`, …) apply. -/
def KonceptDefCCD.toKonceptDefN (d : KonceptDefCCD n α) : KonceptDefN n α where
  definiendum  := d.definiendum
  genus        := d.genus
  differentia  := d.differentia
  isMeet       := d.isMeet
  isEssential  := d.isEssential
  ccd          := d.ccd
  ccd_concept  := d.ccd_concept
  ccd_contrast := d.ccd_contrast

theorem KonceptDefCCD.has_two_units (d : KonceptDefCCD n α) :
    ∃ a b, d.definiendum.pred a ∧ d.definiendum.pred b ∧ a ≠ b :=
  d.toKonceptDefN.has_two_units

/-- **Commensurate essentiality is meaningful.** The admissible
    transformation of a shared CCD is a change of its common unit — one
    rescaling applied to both profiles. Under any such change the
    essentiality verdict is unchanged, for every unit of the definiendum.
    Contrast `raise_flips_under_independent_rescale`: without the shared
    unit, no such invariance exists. Commensuration is exactly what makes
    essentiality a fact rather than an artifact. -/
theorem KonceptDefCCD.essential_rescale (d : KonceptDefCCD n α)
    {c : ℤ} (hc : 0 < c) (a : α) (ha : d.definiendum.pred a) :
    RaiseProd (Point.smul c (d.genus.χ a)) (Point.smul c (d.differentia.χ a)) :=
  (raiseProd_smul_iff hc _ _).mpr (d.isEssential a ha)
