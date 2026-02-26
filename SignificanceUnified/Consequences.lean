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
