import ConceptualSpace

/-!
# Contrast-Derived Characteristic Scales

`Basic.lean` says: "choosing which characteristic defines χ is the hard
epistemological problem — the formalization assumes it is solved externally."

This file stops assuming it. Rand's account of concept-formation runs through
the *Conceptual Common Denominator*: the units of a concept are measured on
the scale on which they differ from their foil — the contrast objects. Tversky
(diagnosticity) and Gärdenfors (context-dependent dimension salience) make the
same move: which dimensions matter for a concept is determined by what the
concept is contrasted against.

Formally: given a shared placement `pos : α → Point n` of entities in a
conceptual space, a concept with unit-set `s` and foil `foil` induces a
**diagnostic weighting** of the dimensions,

  `diagWeightIn pos s foil i = |#foil · Σ_{a∈s} pos a i − #s · Σ_{a∈foil} pos a i|`

(the separation of members from the foil along dimension `i`, scaled by
`#s · #foil` to stay integral), and the concept's **derived characteristic**

  `contrastChiIn pos s foil a = fun i => diagWeightIn pos s foil i * pos a i`.

The scale is *born from the contrast*. What was an unexplained input to
`Koncept`/`KonceptN` becomes a defined term.

## What this makes provable

* **"Everything" has no scale, not just no witness** — a universal concept
  has an empty foil, so its diagnostic weighting is identically zero and its
  derived characteristic collapses; nothing can be similar-by-contrast on it
  (`universal_no_derived_similarity`). This strengthens `no_universal_ccd`:
  previously the universal concept lacked a contrast *witness*; now it lacks
  a *characteristic*. Rand's claim that "existence" has no CCD, as a theorem.

* **Ornamental differentiae have no scale** — if every genus member falls
  under the differentia (the within-genus foil is empty), the differentia's
  derived scale is zero (`ornamental_differentia_no_scale`). A differentia
  must genuinely divide the genus or it measures nothing — the scale-level
  version of `genus_ne_differentia`.

* **Meaningfulness** — diagnostic weights are invariant under translation of
  the entity placement (`diagWeightIn_translate`), and distances on derived
  scales are too (`contrastChiIn_dist_translate`). Similarity judgments on
  contrast-derived scales provably do not depend on the conventional origin
  of the space — extending `Gap.translate` from raw scales to the entire
  scale-construction procedure.

* **Grouping without direction persists** — on the derived scale, the
  incomparable pair of `ConceptualSpace.lean` is still grounded and still
  incomparable (`beastie_derived_ccd`, `beastie_derived_no_direction`):
  deriving the scale from contrast buys grounding, but direction remains
  extra structure, exactly as `witness_hasRaise_fails` showed for raw scales.
-/

variable {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}

-- ══════════════════════════════════════════════════════
-- 1. DIAGNOSTIC WEIGHTS
-- ══════════════════════════════════════════════════════

/-- Diagnosticity of dimension `i` for unit-set `s` against foil `foil`:
    the (integrality-scaled) separation of members from the foil along `i`.
    Equals `#s · #foil · |mean_s(i) − mean_foil(i)|`. -/
def diagWeightIn (pos : α → Point n) (s foil : Finset α) (i : Fin n) : ℕ :=
  ((foil.card : ℤ) * ∑ a ∈ s, pos a i
    - (s.card : ℤ) * ∑ a ∈ foil, pos a i).natAbs

/-- The default foil is everything outside the concept. -/
def diagWeight (pos : α → Point n) (s : Finset α) (i : Fin n) : ℕ :=
  diagWeightIn pos s sᶜ i

/-- No foil, no scale: with an empty foil the diagnostic weighting is
    identically zero. -/
theorem diagWeightIn_empty_foil (pos : α → Point n) (s : Finset α) (i : Fin n) :
    diagWeightIn pos s ∅ i = 0 := by
  simp [diagWeightIn]

/-- No units, no scale either: a scale needs something inside the concept. -/
theorem diagWeightIn_empty_units (pos : α → Point n) (foil : Finset α) (i : Fin n) :
    diagWeightIn pos ∅ foil i = 0 := by
  simp [diagWeightIn]

/-- **A universal concept has no characteristic.** With every entity a unit,
    the foil is empty and the diagnostic weighting vanishes on every
    dimension. -/
theorem diagWeight_univ (pos : α → Point n) (i : Fin n) :
    diagWeight pos Finset.univ i = 0 := by
  simp [diagWeight, diagWeightIn_empty_foil]

/-- **Meaningfulness of the weights.** Diagnostic weights are invariant under
    translation of the entity placement: they measure separation, and
    separation does not see the origin. -/
theorem diagWeightIn_translate (pos : α → Point n) (t : Point n)
    (s foil : Finset α) (i : Fin n) :
    diagWeightIn (fun a => pos a + t) s foil i = diagWeightIn pos s foil i := by
  unfold diagWeightIn
  congr 1
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  ring

-- ══════════════════════════════════════════════════════
-- 2. THE DERIVED CHARACTERISTIC
-- ══════════════════════════════════════════════════════

/-- The contrast-derived characteristic: each entity's position, weighted
    dimension-by-dimension by the concept's diagnosticity against its foil.
    "The scale on which a concept measures its units is the scale on which
    its units differ from their foil." -/
def contrastChiIn (pos : α → Point n) (s foil : Finset α) : α → Point n :=
  fun a i => (diagWeightIn pos s foil i : ℤ) * pos a i

/-- Derived characteristic with the default (complement) foil. -/
def contrastChi (pos : α → Point n) (s : Finset α) : α → Point n :=
  contrastChiIn pos s sᶜ

/-- The concept a unit-set induces once its scale is derived from contrast:
    predicate = membership, characteristic = the derived scale. The "hard
    epistemological problem" field of `KonceptN` is now constructed, not
    assumed. -/
def contrastKoncept (pos : α → Point n) (s : Finset α) : KonceptN n α where
  pred := fun a => a ∈ s
  χ    := contrastChi pos s

/-- **Meaningfulness of derived-scale similarity.** Distances between derived
    placements are invariant under translation of the underlying positions:
    the weights don't move (`diagWeightIn_translate`) and coordinate
    differences don't either. Every CCD-style judgment made on a
    contrast-derived scale is independent of the conventional origin. -/
theorem contrastChiIn_dist_translate (pos : α → Point n) (t : Point n)
    (s foil : Finset α) (a b : α) :
    dist₁ (contrastChiIn (fun x => pos x + t) s foil a)
          (contrastChiIn (fun x => pos x + t) s foil b)
      = dist₁ (contrastChiIn pos s foil a) (contrastChiIn pos s foil b) := by
  unfold dist₁
  apply Finset.sum_congr rfl
  intro i _
  simp only [contrastChiIn, Pi.add_apply, diagWeightIn_translate]
  congr 1
  ring

-- ══════════════════════════════════════════════════════
-- 3. "EVERYTHING" HAS NO SCALE
-- ══════════════════════════════════════════════════════

/-- The universal concept's derived characteristic is the zero scale. -/
theorem contrastChi_univ (pos : α → Point n) (a : α) :
    contrastChi pos Finset.univ a = fun _ => 0 := by
  funext i
  simp [contrastChi, contrastChiIn, Finset.compl_univ, diagWeightIn_empty_foil]

/-- **Strengthening of `no_universal_ccd`.** On the universal concept's
    derived scale, no similarity-by-contrast judgment is possible at all —
    every entity sits at the origin, so the "different degree" conjunct can
    never hold. The universal concept doesn't merely lack a contrast witness;
    it lacks the characteristic on which a witness could be stated. -/
theorem universal_no_derived_similarity (pos : α → Point n) (a b c : α) :
    ¬SimilarByContrastN (contrastChi pos Finset.univ a)
      (contrastChi pos Finset.univ b) (contrastChi pos Finset.univ c) := by
  intro h
  exact h.1 (by rw [contrastChi_univ, contrastChi_univ])

-- ══════════════════════════════════════════════════════
-- 4. ORNAMENTAL DIFFERENTIAE HAVE NO SCALE
--
--    The theoretically right foil for a differentia is not "everything
--    outside it" but the REST OF ITS GENUS: the foil for `rational` in
--    defining Man is the other animals, not rocks. (Aristotle: the
--    differentia divides the genus.) With that foil, a differentia that
--    excludes nothing from the genus measures nothing.
-- ══════════════════════════════════════════════════════

/-- If every genus member falls under the differentia (the within-genus foil
    `g \ s` is empty), the differentia's derived scale is the zero scale. -/
theorem ornamental_differentia_no_scale (pos : α → Point n)
    (g s : Finset α) (hcover : g ⊆ s) (a : α) :
    contrastChiIn pos s (g \ s) a = fun _ => 0 := by
  funext i
  have hempty : g \ s = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hcover
  simp [contrastChiIn, hempty, diagWeightIn_empty_foil]

/-- Hence no similarity judgment is possible on an ornamental differentia's
    scale: a differentia must genuinely divide its genus or it is not a
    characteristic at all — the scale-level version of
    `genus_ne_differentia`. -/
theorem ornamental_differentia_no_similarity (pos : α → Point n)
    (g s : Finset α) (hcover : g ⊆ s) (a b c : α) :
    ¬SimilarByContrastN (contrastChiIn pos s (g \ s) a)
      (contrastChiIn pos s (g \ s) b) (contrastChiIn pos s (g \ s) c) := by
  intro h
  exact h.1 (by rw [ornamental_differentia_no_scale pos g s hcover,
    ornamental_differentia_no_scale pos g s hcover])

-- ══════════════════════════════════════════════════════
-- 5. CONCRETE: THE DERIVED SCALE GROUNDS, BUT STILL
--    DOES NOT DIRECT
-- ══════════════════════════════════════════════════════

inductive Beastie | fox | hen | rock
  deriving DecidableEq, Fintype

def bpos : Beastie → Point 2
  | .fox  => ![0, 1]
  | .hen  => ![1, 0]
  | .rock => ![5, 5]

def beasties : Finset Beastie := {.fox, .hen}

/-- The derived weights: both dimensions are equally diagnostic of
    beastie-hood against the rock (|1·1 − 2·5| = 9 on each). -/
theorem beastie_weights :
    diagWeight bpos beasties 0 = 9 ∧ diagWeight bpos beasties 1 = 9 := by
  constructor <;> decide

/-- On the contrast-derived scale, the fox/hen grouping against the rock is
    grounded: the scale born from the contrast makes the contrast visible. -/
theorem beastie_derived_ccd :
    SimilarByContrastN (contrastChi bpos beasties .fox)
      (contrastChi bpos beasties .hen) (contrastChi bpos beasties .rock) := by
  decide

/-- But deriving the scale from contrast still cannot manufacture direction:
    fox and hen remain incomparable on the derived scale. Grounding comes
    from contrast; direction never does (cf. `witness_hasRaise_fails`). -/
theorem beastie_derived_no_direction :
    ¬RaiseProd (contrastChi bpos beasties .fox) (contrastChi bpos beasties .hen) ∧
    ¬RaiseProd (contrastChi bpos beasties .hen) (contrastChi bpos beasties .fox) := by
  constructor <;> decide
