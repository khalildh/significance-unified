import Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import ProofWidgets.Component.Panel.SelectionPanel  -- registers goalsLocationsToExprs RPC

/-!
# Categorical Reformulation of Significance

The structures in `Basic.lean` are already categorical — this file makes that
explicit using Mathlib's `CategoryTheory` library.

## What this file shows

1. `Koncept α` is a (thin) category — automatic from the `Preorder` instance.
   Morphisms are proofs of `≤` (subset inclusion on extensions).

2. Essential definition yields categorical morphisms:
   `definiendum ⟶ genus` and `definiendum ⟶ differentia`.

3. Barbara is morphism composition: `(S ⟶ M) ≫ (M ⟶ P) = (S ⟶ P)`.

4. The unified significance theorem is a commutative square in `Type`:
   both paths from `AmplificationOver α` to `SignificanceRaise` agree.
-/

open CategoryTheory

-- ══════════════════════════════════════════════════════
-- 1. KONCEPT AS A CATEGORY
--
--    The Preorder instance on Koncept α (Basic.lean §2) gives us
--    SmallCategory automatically via Mathlib's preorder-to-category
--    construction. Morphisms Hom(c, d) = ULift(PLift(c ≤ d)).
-- ══════════════════════════════════════════════════════

-- The SmallCategory instance is already synthesized from Preorder.
-- We can verify it:
example (α : Type) : SmallCategory (Koncept α) := inferInstance

-- ══════════════════════════════════════════════════════
-- 2. ESSENTIAL DEFINITION AS CATEGORICAL MORPHISMS
--
--    definiendum ≤ genus and definiendum ≤ differentia
--    become morphisms in the thin category.
-- ══════════════════════════════════════════════════════

/-- The morphism from definiendum to genus in the Koncept category. -/
def KonceptDef.genusMor {α : Type} (d : KonceptDef α) :
    d.definiendum ⟶ d.genus :=
  homOfLE (definiendum_le_genus d)

/-- The morphism from definiendum to differentia in the Koncept category. -/
def KonceptDef.differentiaMor {α : Type} (d : KonceptDef α) :
    d.definiendum ⟶ d.differentia :=
  homOfLE (definiendum_le_differentia d)

-- ══════════════════════════════════════════════════════
-- 3. BARBARA AS MORPHISM COMPOSITION
--
--    Barbara (AAA-1) says: S ≤ M and M ≤ P implies S ≤ P.
--    Categorically: (S ⟶ M) ≫ (M ⟶ P) = (S ⟶ P).
--    In a thin category every diagram commutes, so this
--    is trivially a compositional structure.
-- ══════════════════════════════════════════════════════

/-- Barbara is morphism composition in the Koncept category. -/
def Barbara.asMorphismComposition {α : Type} (b : Barbara α) :
    b.S ⟶ b.P :=
  homOfLE b.allSareM ≫ homOfLE b.allMareP

/-- The composed morphism equals the direct conclusion morphism. -/
theorem Barbara.composition_eq_conclusion {α : Type} (b : Barbara α) :
    Barbara.asMorphismComposition b = homOfLE b.conclusion := by
  -- In a thin category, any two parallel morphisms are equal
  rfl

-- ══════════════════════════════════════════════════════
-- 4. DEFINITION CHAINS AS MORPHISM CHAINS
--
--    If d₁.differentia = d₂.genus (definition refines),
--    the composed morphism definiendum₁ ⟶ differentia₂
--    factors through the intermediate concept.
-- ══════════════════════════════════════════════════════

/-- A definition chain: the differentia of one definition
    serves as the genus of a refinement. -/
def KonceptDef.chainMor {α : Type} (d₁ d₂ : KonceptDef α)
    (_hlink : d₁.differentia = d₂.genus)
    (hle : d₁.definiendum ≤ d₂.definiendum) :
    d₁.definiendum ⟶ d₂.definiendum :=
  homOfLE hle

-- ══════════════════════════════════════════════════════
-- 5. MEET AS A CATEGORICAL PRODUCT
--
--    meet_le_left, meet_le_right, and meet_universal say
--    that c.meet d is a categorical product (in a preorder,
--    this is the greatest lower bound = infimum).
-- ══════════════════════════════════════════════════════

/-- The meet projections as morphisms. -/
noncomputable def Koncept.meetProj₁ {α : Type} (c d : Koncept α) :
    c.meet d ⟶ c :=
  homOfLE (meet_le_left c d)

noncomputable def Koncept.meetProj₂ {α : Type} (c d : Koncept α) :
    c.meet d ⟶ d :=
  homOfLE (meet_le_right c d)

/-- The universal property of meet: any concept below both factors
    through the meet. -/
noncomputable def Koncept.meetUniv {α : Type} {c d e : Koncept α}
    (f : e ⟶ c) (g : e ⟶ d) : e ⟶ c.meet d :=
  homOfLE (meet_universal (leOfHom f) (leOfHom g))

-- ══════════════════════════════════════════════════════
-- 6. UNIFIED SIGNIFICANCE AS A COMMUTATIVE SQUARE
--
--    The two paths from AmplificationOver α to SignificanceRaise
--    agree on (baseline, subject). We express this as a
--    CommSq in the category Type.
-- ══════════════════════════════════════════════════════

/-- Extract a SignificanceRaise via the Kennedy (amplification) path. -/
noncomputable def kennedyPath {α : Type} (ao : AmplificationOver α) :
    SignificanceRaise :=
  ao.move.toSignificanceRaise

/-- Extract a SignificanceRaise via the Rand (essential definition) path:
    first convert to KonceptDefWithUnit, then embed. -/
noncomputable def randPath {α : Type} (ao : AmplificationOver α) :
    SignificanceRaise :=
  (fromAmpOver ao).1.toSignificanceRaise ao.entity ao.inDef

/-- The two paths produce identical baseline and subject values. -/
theorem unified_significance_fields {α : Type} (ao : AmplificationOver α) :
    (kennedyPath ao).baseline = (randPath ao).baseline ∧
    (kennedyPath ao).subject = (randPath ao).subject :=
  unified_significance ao

-- For the full commutative square, we work in the category Type.
-- The four corners are:
--   KonceptDefWithUnit α  ──toAmpOver──→  AmplificationOver α
--          |                                       |
--     randExtract                             kennedyExtract
--          |                                       |
--          v                                       v
--    SignificanceRaise  ══════════════  SignificanceRaise
--
-- where the bottom "morphism" is the identity (both paths land
-- in the same SignificanceRaise value).

/-- Extract a SignificanceRaise from a KonceptDefWithUnit. -/
noncomputable def randExtract {α : Type} (x : KonceptDefWithUnit α) :
    SignificanceRaise :=
  x.1.toSignificanceRaise x.2.1 x.2.2

/-- Extract a SignificanceRaise from an AmplificationOver. -/
noncomputable def kennedyExtract {α : Type} (ao : AmplificationOver α) :
    SignificanceRaise :=
  ao.move.toSignificanceRaise

/-- The unified significance square: both paths from
    KonceptDefWithUnit to SignificanceRaise agree.

    This says: kennedyExtract ∘ toAmpOver = randExtract
    i.e., going through amplification and then extracting the raise
    gives the same result as directly extracting from the definition. -/
theorem unified_square_commutes {α : Type} (x : KonceptDefWithUnit α) :
    kennedyExtract (toAmpOver x) = randExtract x := by
  simp [kennedyExtract, randExtract, AmplificationMove.toSignificanceRaise,
        KonceptDef.toSignificanceRaise, toAmpOver]

-- ══════════════════════════════════════════════════════
-- 7. CONCRETE EXAMPLES
-- ══════════════════════════════════════════════════════

/-- The morphism "all men are animals" in the Koncept category. -/
noncomputable def allMenAreAnimals_mor :
    konceptMan ⟶ konceptAnimal :=
  defMan.genusMor

/-- The morphism "all men are rational" in the Koncept category. -/
noncomputable def allMenAreRational_mor :
    konceptMan ⟶ konceptRational :=
  defMan.differentiaMor

/-- Man factors through the meet of Animal and Rational (its definition). -/
noncomputable def manFactorsMeet :
    konceptMan ⟶ konceptAnimal.meet konceptRational :=
  Koncept.meetUniv allMenAreAnimals_mor allMenAreRational_mor

/-- The unified square commutes for the Man example. -/
noncomputable example :
    kennedyExtract (toAmpOver manUnit) = randExtract manUnit :=
  unified_square_commutes manUnit

-- ══════════════════════════════════════════════════════
-- 8. COMMDIAG WIDGET EXAMPLES
--
--    Place your cursor on the `skip` lines below in VS Code.
--    The GoalTypePanel widget renders commutative diagrams
--    for goals of the form f ≫ g = h (triangle) or
--    f ≫ g = i ≫ h (square).
-- ══════════════════════════════════════════════════════

open ProofWidgets

set_option linter.unusedTactic false in
/-- Essential definition triangle: Man is defined as the meet of Animal
    and Rational, so Man ⟶ Animal ⟶ Animal factors through itself.
    Shows: definiendum → genus → super = definiendum → super -/
noncomputable example {α : Type} (d : KonceptDef α)
    (super : Koncept α) (h : d.genus ≤ super) :
    d.genusMor ≫ homOfLE h = homOfLE (le_trans (definiendum_le_genus d) h) := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here to see triangle
  sorry

set_option linter.unusedTactic false in
/-- Barbara syllogism as a commutative triangle:
    (Man ⟶ Man) ≫ (Man ⟶ Animal) = (Man ⟶ Animal)
    "All S are M, all M are P, therefore all S are P" -/
noncomputable example :
    (𝟙 konceptMan) ≫ allMenAreAnimals_mor = allMenAreAnimals_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: Barbara triangle
  sorry

set_option linter.unusedTactic false in
/-- Definition square: Man sits below both Animal and Rational.
    genusMor ≫ (Animal ⟶ Animal) = differentiaMor ≫ (Rational ⟶ Animal)?
    This is NOT generally true — it shows the two arms of the definition
    as a diagram the widget can render. -/
noncomputable example {α : Type} (d : KonceptDef α)
    (h : d.differentia ≤ d.genus) :
    d.genusMor ≫ (𝟙 d.genus) = d.differentiaMor ≫ homOfLE h := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: definition square
  sorry

set_option linter.unusedTactic false in
/-- The concrete Man example: konceptMan maps to both konceptAnimal
    and konceptRational. Two Barbara syllogisms from one definition. -/
noncomputable example :
    allMenAreAnimals_mor ≫ (𝟙 konceptAnimal) = allMenAreAnimals_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: Man → Animal triangle
  sorry

set_option linter.unusedTactic false in
/-- Commutative square with four abstract Koncepts.
    The general shape the widget renders. -/
example {α : Type} {A B C D : Koncept α}
    (f : A ⟶ B) (g : B ⟶ D) (i : A ⟶ C) (h : C ⟶ D) :
    f ≫ g = i ≫ h := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: abstract square
  sorry
