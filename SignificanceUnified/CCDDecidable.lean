import ConceptualSpace

/-!
# Decidability of `CCD₃N`

`CCD₃N` is a bounded `∀`-pairs / `∃`-witness proposition over a finite entity
type, so it is decidable — but the strict-implicit binders `∀ ⦃a b⦄` in its
definition block Lean's automatic `Fintype` instance. This routes through the
definitionally-equal explicit-binder form so `decide` works on the actual
`CCD₃N k`. It is what lets the generated `ValidateComposed.lean` cross-check the
Python audit's per-concept grounding DECISION (not just the primitives) against
the kernel.
-/

instance CCD₃N.decidableInst {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    {k : KonceptN n α} [DecidablePred k.pred] : Decidable (CCD₃N k) := by
  have h : CCD₃N k = (∀ a b, k.pred a → k.pred b → a ≠ b →
      ∃ c, ¬k.pred c ∧ SimilarByContrastN (k.χ a) (k.χ b) (k.χ c)) := rfl
  rw [h]; infer_instance
