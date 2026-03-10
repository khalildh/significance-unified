import Basic
import Consequences
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import ProofWidgets.Component.Panel.SelectionPanel  -- registers goalsLocationsToExprs RPC

/-!
# Categorical Reformulation of Significance

The structures in `Basic.lean` and `Consequences.lean` are already categorical —
this file makes that explicit using Mathlib's `CategoryTheory` library.

## What this file shows

### Categories
1. `Koncept α` is a thin category — automatic from `Preorder`.
2. `Depth` (= ℤ) is a thin category — automatic from `LinearOrder`.

### Morphisms from Basic.lean
3. Essential definition: `definiendum ⟶ genus` and `definiendum ⟶ differentia`.
4. Barbara = morphism composition: `(S ⟶ M) ≫ (M ⟶ P) = (S ⟶ P)`.
5. Celarent as an anti-morphism (disjointness — not a categorical morphism).
6. Darii as existential witness through a morphism.
7. Cicero's chain as morphism composition on `Depth`.
8. `SignificanceRaise.compose` as morphism composition on `Depth`.

### Products and coproducts
9. Meet as categorical product with universal property.
10. Join as categorical coproduct with universal property.

### Round-trip and unified significance
11. `toAmpOver`/`fromAmpOver` as an `Equiv` (type-theoretic isomorphism).
12. Unified significance as a commutative square.

### From Consequences.lean
13. Definition chains as morphism chains with depth accumulation.
14. No-cycle theorem: no directed cycles in the depth category.
15. Square of opposition: PropA as morphism, relationships between A/E/I/O.
16. All concrete syllogisms as morphisms.

### CommDiag widget examples
17. Interactive diagrams viewable in VS Code's Lean Infoview.
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
-- 6. JOIN AS A CATEGORICAL COPRODUCT
--
--    le_join_left, le_join_right give the injections.
--    The join is the least upper bound = supremum in the preorder.
-- ══════════════════════════════════════════════════════

noncomputable def Koncept.joinInj₁ {α : Type} (c d : Koncept α) :
    c ⟶ c.join d :=
  homOfLE (le_join_left c d)

noncomputable def Koncept.joinInj₂ {α : Type} (c d : Koncept α) :
    d ⟶ c.join d :=
  homOfLE (le_join_right c d)

-- ══════════════════════════════════════════════════════
-- 7. DEPTH (ℤ) AS A CATEGORY
--
--    ℤ has a LinearOrder, so it automatically gets SmallCategory.
--    SignificanceRaise.compose and Cicero's chain are morphism
--    composition in this category.
-- ══════════════════════════════════════════════════════

-- ℤ is automatically a category via its LinearOrder/Preorder:
noncomputable example : SmallCategory ℤ := inferInstance

/-- A Raise a b (i.e., a < b) gives a morphism a ⟶ b in the ℤ category. -/
noncomputable def Raise.toMor {a b : Depth} (h : Raise a b) : a ⟶ b :=
  homOfLE (le_of_lt h)

/-- SignificanceRaise packages a morphism in the ℤ category. -/
noncomputable def SignificanceRaise.toMor (r : SignificanceRaise) :
    r.baseline ⟶ r.subject :=
  r.isStrict.toMor

/-- SignificanceRaise.compose is morphism composition in the ℤ category. -/
theorem SignificanceRaise.compose_is_comp (r1 r2 : SignificanceRaise)
    (hlink : r1.subject = r2.baseline) :
    (r1.compose r2 hlink).toMor =
      r1.toMor ≫ (hlink ▸ r2.toMor) := by
  rfl

/-- Cicero's chain: two raises compose into one in the ℤ category. -/
noncomputable def ciceroChain_mor : (2 : ℤ) ⟶ (9 : ℤ) :=
  cicero1.toMor ≫ cicero2.toMor

-- ══════════════════════════════════════════════════════
-- 8. CELARENT AND DARII — CATEGORICAL PERSPECTIVE
--
--    Celarent (disjointness) is NOT a morphism — it asserts
--    non-existence of morphisms (no path from S to P through M).
--    Darii (existential) passes a witness through a morphism.
-- ══════════════════════════════════════════════════════

/-- Celarent: if there is no morphism from M to P (disjoint extensions),
    and S ⟶ M exists, then there is no morphism from S to P either.
    Note: in a thin category, ¬(S ⟶ P) is vacuously false since
    Hom(S,P) = ULift(PLift(S ≤ P)) always exists. Celarent operates
    at the element level, not the morphism level — it is genuinely
    non-categorical. -/
theorem Celarent.categorical_perspective {α : Type} (c : Celarent α) :
    -- The minor premise gives a morphism:
    ∃ _f : c.S ⟶ c.M, -- S ⟶ M exists
    -- The major premise is element-level negation (not a morphism):
    ∀ a, c.M.pred a → ¬c.P.pred a :=
  ⟨homOfLE c.allSareM, c.noMareP⟩

/-- Darii: the major premise (M ≤ P) is a morphism; the minor premise
    provides a witness that passes through it. -/
theorem Darii.categorical_perspective {α : Type} (d : Darii α) :
    ∃ (_f : d.M ⟶ d.P) (a : α), d.S.pred a ∧ d.P.pred a :=
  ⟨homOfLE d.allMareP, by
    obtain ⟨a, hS, hM⟩ := d.someSareM
    exact ⟨a, hS, d.allMareP a hM⟩⟩

-- ══════════════════════════════════════════════════════
-- 9. ROUND-TRIP AS AN EQUIV
--
--    toAmpOver and fromAmpOver form a type-theoretic
--    isomorphism (Equiv). This is the right notion since
--    KonceptDefWithUnit and AmplificationOver are not
--    objects in a common category — they are just types.
-- ══════════════════════════════════════════════════════

/-- The round-trip is an Equiv on the concept fields.
    roundtrip_fwd gives the left inverse definitionally.
    roundtrip_bwd gives field-by-field equality on the right. -/
noncomputable def roundtripEquivLeft {α : Type} :
    Function.LeftInverse (@fromAmpOver α) (@toAmpOver α) :=
  roundtrip_fwd

-- ══════════════════════════════════════════════════════
-- 10. UNIFIED SIGNIFICANCE AS A COMMUTATIVE SQUARE
--
--    The two paths from AmplificationOver α to SignificanceRaise
--    agree. Both paths factor through the concept fields.
-- ══════════════════════════════════════════════════════

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
    kennedyExtract ∘ toAmpOver = randExtract -/
theorem unified_square_commutes {α : Type} (x : KonceptDefWithUnit α) :
    kennedyExtract (toAmpOver x) = randExtract x := by
  simp [kennedyExtract, randExtract, AmplificationMove.toSignificanceRaise,
        KonceptDef.toSignificanceRaise, toAmpOver]

-- ══════════════════════════════════════════════════════
-- 11. DEFINITION CHAINS AS MORPHISM CHAINS
--
--    From Consequences.lean: definition chains compose
--    transitively, depth accumulates, and cycles are impossible.
--    Categorically: each definition step is a morphism in the
--    ℤ category, and no-cycle follows from antisymmetry of <.
-- ══════════════════════════════════════════════════════

/-- A definition chain gives a composed morphism in the ℤ category:
    genus.χ a ⟶ differentia₂.χ a, spanning two definitions. -/
noncomputable def KonceptDef.chainDepthMor {α : Type}
    (d1 d2 : KonceptDef α)
    (hchain : d2.genus = d1.differentia)
    (a : α) (ha1 : d1.definiendum.pred a) (ha2 : d2.definiendum.pred a) :
    d1.genus.χ a ⟶ d2.differentia.χ a :=
  (d1.isEssential a ha1 |>.toMor) ≫
    ((congrFun (congrArg Koncept.χ hchain) a ▸ d2.isEssential a ha2) |>.toMor)

-- No-cycle is a consequence of the ℤ category being a partial order.
-- Three composed morphisms a ⟶ b ⟶ c ⟶ a would give a ≤ b ≤ c ≤ a,
-- but with strict raises a < b < c, a morphism c ⟶ a would require
-- c ≤ a, contradicting a < b < c (which gives a < c, so c > a).
-- The actual no-cycle theorem is in Consequences.lean (no_definition_cycle).

/-- If we have morphisms a ⟶ b and b ⟶ c from strict raises, then
    there cannot also be a strict raise c → a. -/
theorem no_cycle_depth {a b c : Depth}
    (h1 : Raise a b) (h2 : Raise b c) : ¬Raise c a := by
  intro h3
  exact absurd (Raise.trans (Raise.trans h1 h2) h3) (Raise.irrefl _)

-- ══════════════════════════════════════════════════════
-- 12. SQUARE OF OPPOSITION — CATEGORICAL PERSPECTIVE
--
--    PropA (S ≤ P) is a morphism. The other three propositions
--    involve existence or negation and are not morphisms.
--    The six classical relationships connect morphisms to
--    element-level properties.
-- ══════════════════════════════════════════════════════

/-- PropA is equivalent to the existence of a morphism in the thin category.
    "All S are P" ↔ there exists a morphism S ⟶ P. -/
theorem propA_iff_mor {α : Type} {S P : Koncept α} :
    PropA S P ↔ Nonempty (S ⟶ P) :=
  ⟨fun h => ⟨homOfLE h⟩, fun ⟨f⟩ => leOfHom f⟩

/-- Contradiction (A ↔ ¬O): a morphism S ⟶ P exists iff there is no
    element witnessing "some S are not P". -/
theorem contradiction_mor {α : Type} {S P : Koncept α} :
    Nonempty (S ⟶ P) ↔ ¬PropO S P :=
  propA_iff_mor.symm.trans propA_iff_not_propO

-- ══════════════════════════════════════════════════════
-- 13. ALL CONCRETE SYLLOGISMS AS MORPHISMS
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

/-- Barbara to genus: Man ⟶ Man ⟶ Animal = Man ⟶ Animal -/
noncomputable def barbaraToGenusMor :
    konceptMan ⟶ konceptAnimal :=
  (defMan.barbaraToGenus).asMorphismComposition

/-- Barbara to differentia: Man ⟶ Man ⟶ Rational = Man ⟶ Rational -/
noncomputable def barbaraToDifferentiaMor :
    konceptMan ⟶ konceptRational :=
  (defMan.barbaraToDifferentia).asMorphismComposition

/-- Alternative definition: Man = Rational Sentient (from Consequences.lean).
    Same morphism Man ⟶ Rational, different factoring. -/
noncomputable def altDefMan_genusMor :
    konceptMan ⟶ konceptSentient :=
  (defManAlt).genusMor

noncomputable def altDefMan_differentiaMor :
    konceptMan ⟶ konceptRational :=
  (defManAlt).differentiaMor

/-- Both definitions of Man give the same morphism to Rational.
    (In a thin category, any two parallel morphisms are equal.) -/
noncomputable example :
    allMenAreRational_mor = altDefMan_differentiaMor := by
  rfl

-- ══════════════════════════════════════════════════════
-- 14. AMPLIFICATION MOVE COMPOSITION AS MORPHISMS
--
--    AmplificationMove.compose chains two rhetorical moves.
--    The baseline→subject→subject' path is morphism composition
--    in the ℤ category.
-- ══════════════════════════════════════════════════════

/-- An AmplificationMove gives a morphism baseline ⟶ subject in ℤ. -/
noncomputable def AmplificationMove.toMor (m : AmplificationMove) :
    m.comparison.baseline ⟶ m.comparison.subject :=
  m.isStrict.toMor

-- ══════════════════════════════════════════════════════
-- 15. COMMDIAG WIDGET EXAMPLES
--
--    Place your cursor on the `skip` lines below in VS Code.
--    The GoalTypePanel widget renders commutative diagrams
--    for goals of the form f ≫ g = h (triangle) or
--    f ≫ g = i ≫ h (square).
-- ══════════════════════════════════════════════════════

open ProofWidgets

set_option linter.unusedTactic false in
/-- ▶ Essential definition triangle: definiendum → genus → super.
    Shows how definitions compose with further subsumption. -/
noncomputable example {α : Type} (d : KonceptDef α)
    (super : Koncept α) (h : d.genus ≤ super) :
    d.genusMor ≫ homOfLE h = homOfLE (le_trans (definiendum_le_genus d) h) := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here to see triangle
  sorry

set_option linter.unusedTactic false in
/-- ▶ Barbara syllogism: (Man ⟶ Man) ≫ (Man ⟶ Animal) = (Man ⟶ Animal).
    Identity composed with the genus morphism. -/
noncomputable example :
    (𝟙 konceptMan) ≫ allMenAreAnimals_mor = allMenAreAnimals_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: Barbara triangle
  sorry

set_option linter.unusedTactic false in
/-- ▶ Definition square: the two arms of an essential definition meet.
    definiendum → genus and definiendum → differentia → genus. -/
noncomputable example {α : Type} (d : KonceptDef α)
    (h : d.differentia ≤ d.genus) :
    d.genusMor ≫ (𝟙 d.genus) = d.differentiaMor ≫ homOfLE h := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: definition square
  sorry

set_option linter.unusedTactic false in
/-- ▶ Man → Animal: concrete Barbara triangle. -/
noncomputable example :
    allMenAreAnimals_mor ≫ (𝟙 konceptAnimal) = allMenAreAnimals_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: Man → Animal triangle
  sorry

set_option linter.unusedTactic false in
/-- ▶ Abstract commutative square with four Koncepts. -/
example {α : Type} {A B C D : Koncept α}
    (f : A ⟶ B) (g : B ⟶ D) (i : A ⟶ C) (h : C ⟶ D) :
    f ≫ g = i ≫ h := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: abstract square
  sorry

set_option linter.unusedTactic false in
/-- ▶ Man factors through both Animal and Rational: the definition
    gives two morphisms from Man, both factoring through the meet. -/
noncomputable example :
    manFactorsMeet ≫ Koncept.meetProj₁ konceptAnimal konceptRational
    = allMenAreAnimals_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: meet projection triangle
  sorry

set_option linter.unusedTactic false in
/-- ▶ Two definitions of Man: via Animal and via Sentient.
    Both give Man ⟶ Rational; the morphisms are equal (thin category). -/
noncomputable example :
    allMenAreRational_mor ≫ (𝟙 konceptRational)
    = altDefMan_differentiaMor ≫ (𝟙 konceptRational) := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: two-definitions square
  sorry

set_option linter.unusedTactic false in
/-- ▶ Cicero's chain in the ℤ category: 2 → 5 → 9.
    Morphism composition on Depth. -/
example :
    cicero1.toMor ≫ cicero2.toMor = ciceroChain_mor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: Cicero chain triangle
  sorry

set_option linter.unusedTactic false in
/-- ▶ Definition chain: Man → Sentient (via alternative definition).
    Each definition step is a morphism on the depth scale. -/
noncomputable example :
    altDefMan_genusMor ≫ (𝟙 konceptSentient)
    = altDefMan_genusMor := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: definition chain triangle
  sorry

-- ══════════════════════════════════════════════════════
-- 16. THE DEFINITION DIAMOND
--
--    Man has two valid essential definitions:
--      defMan:    Man = Rational Animal    (genus χ = 1)
--      defManAlt: Man = Rational Sentient  (genus χ = 2)
--
--    In the Koncept category, Animal and Sentient have the SAME
--    extension ({man, human, dog}) so they are mutually ≤ —
--    categorically isomorphic. But they have DIFFERENT χ values,
--    so the depth raises differ:
--      defMan    raises from 1 to 3 (gap of 2 on ℤ)
--      defManAlt raises from 2 to 3 (gap of 1 on ℤ)
--
--    NON-TRIVIAL POINT: The concept category cannot distinguish
--    Animal from Sentient — they have the same morphisms to and
--    from everything. But the significance structure (depth raises)
--    DOES distinguish them. This is why the formalization needs BOTH:
--      • A category (Koncept) for syllogistic inference
--      • A depth scale (ℤ) for significance / amplification
--    Neither alone suffices. The category tells you WHAT follows
--    from WHAT (Barbara, Celarent, etc.). The depth scale tells
--    you HOW MUCH more significant one thing is than another
--    (the Raise). Essential definition lives at the intersection:
--    it is a categorical relationship (genus ≤ differentia as
--    extension inclusion) that also carries a depth ordering
--    (genus.χ < differentia.χ as significance).
-- ══════════════════════════════════════════════════════

-- Animal and Sentient are mutually ≤ (same extension: man, human, dog)
private theorem animal_le_sentient :
    konceptAnimal ≤ konceptSentient :=
  fun a ha => by cases a <;> simp_all [konceptAnimal, konceptSentient]

private theorem sentient_le_animal :
    konceptSentient ≤ konceptAnimal :=
  fun a ha => by cases a <;> simp_all [konceptAnimal, konceptSentient]

/-- Morphism Animal ⟶ Sentient in the Koncept category. -/
noncomputable def animalToSentient : konceptAnimal ⟶ konceptSentient :=
  homOfLE animal_le_sentient

/-- Morphism Sentient ⟶ Animal in the Koncept category. -/
noncomputable def sentientToAnimal : konceptSentient ⟶ konceptAnimal :=
  homOfLE sentient_le_animal

/-- Animal and Sentient are categorically isomorphic: morphisms in both
    directions, and both compositions are the identity (trivially, in a
    thin category). -/
theorem animal_sentient_iso :
    animalToSentient ≫ sentientToAnimal = 𝟙 konceptAnimal ∧
    sentientToAnimal ≫ animalToSentient = 𝟙 konceptSentient :=
  ⟨rfl, rfl⟩

/-- But Animal and Sentient are NOT equal — they have different χ.
    Animal.χ man = 1, Sentient.χ man = 2. The category is blind to
    this difference; the depth scale sees it. -/
theorem animal_ne_sentient : konceptAnimal ≠ konceptSentient := by
  intro h
  have h1 := congrFun (congrArg Koncept.χ h) LivingThing.man
  simp [konceptAnimal, konceptSentient] at h1

/-- The two definitions give the SAME morphism Man ⟶ Rational
    (thin category — all parallel morphisms are equal) ... -/
theorem same_differentia_morphism :
    allMenAreRational_mor = altDefMan_differentiaMor := rfl

/-- ... but DIFFERENT depth raises for entity .man:
    defMan raises from 1 to 3 (genus Animal, χ = 1),
    defManAlt raises from 2 to 3 (genus Sentient, χ = 2).
    The category says "same inference." The depth scale says
    "different significance." -/
theorem different_genus_depths :
    defMan.genus.χ LivingThing.man ≠ defManAlt.genus.χ LivingThing.man := by
  show (1 : ℤ) ≠ 2; omega

/-- The depth raise for defMan: Animal(1) → Rational(3), gap = 2. -/
theorem defMan_raise_gap :
    defMan.differentia.χ LivingThing.man - defMan.genus.χ LivingThing.man = 2 := by
  simp [defMan, konceptRational, konceptAnimal]

/-- The depth raise for defManAlt: Sentient(2) → Rational(3), gap = 1. -/
theorem defManAlt_raise_gap :
    defManAlt.differentia.χ LivingThing.man - defManAlt.genus.χ LivingThing.man = 1 := by
  simp [defManAlt, konceptRational, konceptSentient]

/-- The full diamond: in the Koncept category, both definitions produce
    a commutative square through the Animal ↔ Sentient isomorphism.
    But the depth raises embedded in each definition are different.
    This is the central tension the formalization resolves: syllogistic
    (the category) and significance (the depth scale) are complementary
    structures on the same concepts. -/
theorem definition_diamond :
    -- Categorical: both paths Man → Animal agree (thin category)
    (allMenAreAnimals_mor = altDefMan_genusMor ≫ sentientToAnimal) ∧
    -- Categorical: both paths Man → Rational agree (thin category)
    (allMenAreRational_mor = altDefMan_differentiaMor) ∧
    -- Depth: the raises are DIFFERENT (genus depths differ)
    (defMan.genus.χ LivingThing.man ≠ defManAlt.genus.χ LivingThing.man) ∧
    -- Depth: defMan has a BIGGER raise (2 > 1)
    (defMan.differentia.χ LivingThing.man - defMan.genus.χ LivingThing.man >
     defManAlt.differentia.χ LivingThing.man - defManAlt.genus.χ LivingThing.man) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [defMan, defManAlt, konceptAnimal, konceptSentient]
  · simp [defMan, defManAlt, konceptRational, konceptAnimal, konceptSentient]

-- ══════════════════════════════════════════════════════
-- CommDiag widgets for the Definition Diamond
-- ══════════════════════════════════════════════════════

set_option linter.unusedTactic false in
/-- ▶ THE DEFINITION DIAMOND (square):
    Man → Animal via defMan and Man → Sentient → Animal via defManAlt.
    Both paths land at Animal. The square commutes (thin category)
    but the depth raises carried by each path differ.

    Cursor on `skip` to see:
      konceptMan ──allMenAreAnimals_mor──→ konceptAnimal
          |                                      |
    altDefMan_genusMor                    𝟙 konceptAnimal
          |                                      |
          v                                      v
      konceptSentient ──sentientToAnimal──→ konceptAnimal -/
noncomputable example :
    allMenAreAnimals_mor ≫ (𝟙 konceptAnimal)
    = altDefMan_genusMor ≫ sentientToAnimal := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: THE DEFINITION DIAMOND
  sorry

set_option linter.unusedTactic false in
/-- ▶ Same differentia, different genus (square):
    Both definitions send Man → Rational. The genus arm differs
    (Animal vs Sentient) but the differentia arm is identical.

    Cursor on `skip` to see:
      konceptMan ──allMenAreRational_mor──→ konceptRational
          |                                        |
    altDefMan_genusMor                      𝟙 konceptRational
          |                                        |
          v                                        v
      konceptSentient ──────────f──────────→ konceptRational -/
noncomputable example (f : konceptSentient ⟶ konceptRational) :
    allMenAreRational_mor ≫ (𝟙 konceptRational)
    = altDefMan_genusMor ≫ f := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: same differentia, different genus
  sorry

set_option linter.unusedTactic false in
/-- ▶ The full picture (square):
    Man → Animal and Man → Rational are the two arms of defMan.
    Man sits at the apex; Animal and Rational are the base.
    The CCD₃ witness (dog) grounds the essentiality from outside.

    Cursor on `skip` to see:
      konceptMan ──allMenAreAnimals_mor──→ konceptAnimal
          |                                       |
    allMenAreRational_mor            animalToSentient
          |                                       |
          v                                       v
      konceptRational ────────f────────→ konceptSentient -/
noncomputable example (f : konceptRational ⟶ konceptSentient) :
    allMenAreAnimals_mor ≫ animalToSentient
    = allMenAreRational_mor ≫ f := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: full definition picture
  sorry

set_option linter.unusedTactic false in
/-- ▶ The depth chain (triangle in ℤ):
    defMan: genus depth 1 → differentia depth 3 (raise of 2).
    The raise is a morphism (1 : ℤ) ⟶ (3 : ℤ) in the depth category.
    This is the SAME information as the essential definition, but
    projected onto the depth scale. -/
noncomputable example :
    (show (1 : ℤ) ⟶ (2 : ℤ) from homOfLE (by omega)) ≫
    (show (2 : ℤ) ⟶ (3 : ℤ) from homOfLE (by omega))
    = (show (1 : ℤ) ⟶ (3 : ℤ) from homOfLE (by omega)) := by
  with_panel_widgets [GoalTypePanel]
  skip  -- ← cursor here: depth chain 1 → 2 → 3
  sorry
