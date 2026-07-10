import Basic
import Consequences
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Functors Between Concept Categories

`CategoryTheory.lean` observes that `Koncept α` is a thin category. Inside a
single thin category, category theory adds vocabulary but no power: every
diagram commutes. The categorical content lives *between* categories — in
functors, and in what they preserve.

This file provides the two basic functors of the concept framework:

1. **Change of universe** (`Koncept.comapFunctor`): a map of universes
   `f : α → β` contravariantly pulls concepts on `β` back to concepts on
   `α`, preserving subsumption. Pullback is strictly functorial
   (`comap_id`, `comap_comp`) — so `Koncept` is a presheaf of preorders on
   the category of types.

2. **Extension** (`Koncept.extensionFunctor`): the forgetful functor from
   concepts to sets of entities. This is the functor the FCA bridge
   (`FCA.lean`) factors through — it forgets χ, keeps membership.

Plus the transport result that gives change-of-universe its epistemological
reading: CCD witnesses pull back (`CCDWitness₃.comap`). Contrast-grounding
is stable under re-description of the universe: if a concept is grounded
over `β` and the witnessing entities are visible through `f`, the pulled-back
concept is grounded over `α`. Depth values, gaps, and similarity relations
are all preserved on the nose because the pulled-back χ *is* `χ ∘ f`.
-/

open CategoryTheory

variable {α β γ : Type}

-- ══════════════════════════════════════════════════════
-- 1. CHANGE OF UNIVERSE: PULLBACK OF CONCEPTS
-- ══════════════════════════════════════════════════════

/-- Pull a concept on `β` back along `f : α → β`: an entity falls under the
    pulled-back concept iff its image falls under the original, and its
    depth is its image's depth. -/
def Koncept.comap (f : α → β) (k : Koncept β) : Koncept α where
  pred := fun a => k.pred (f a)
  χ    := fun a => k.χ (f a)

/-- Pullback preserves subsumption: `comap f` is monotone. -/
theorem Koncept.comap_mono (f : α → β) :
    Monotone (Koncept.comap f) :=
  fun _ _ h a ha => h (f a) ha

/-- Pullback is a functor between concept categories (contravariant in the
    universe): `Koncept β ⥤ Koncept α`. -/
def Koncept.comapFunctor (f : α → β) : Koncept β ⥤ Koncept α :=
  (Koncept.comap_mono f).functor

/-- Pullback along the identity is the identity — on the nose. -/
theorem Koncept.comap_id (k : Koncept α) :
    Koncept.comap id k = k := rfl

/-- Pullback along a composite is the composite of pullbacks — on the nose.
    Together with `comap_id` this makes `Koncept` a strict presheaf of
    preorders on the category of types. -/
theorem Koncept.comap_comp (f : α → β) (g : β → γ) (k : Koncept γ) :
    Koncept.comap (g ∘ f) k = Koncept.comap f (Koncept.comap g k) := rfl

/-- The functor versions of the presheaf laws. -/
theorem Koncept.comapFunctor_id :
    Koncept.comapFunctor (id : α → α) = 𝟭 (Koncept α) := rfl

theorem Koncept.comapFunctor_comp (f : α → β) (g : β → γ) :
    Koncept.comapFunctor (g ∘ f)
      = Koncept.comapFunctor g ⋙ Koncept.comapFunctor f := rfl

/-- Pullback commutes with meet: `comap` preserves the conjunctive
    structure of concepts, not just the order. -/
theorem Koncept.comap_meet (f : α → β) (c d : Koncept β) :
    Koncept.comap f (c.meet d) = (Koncept.comap f c).meet (Koncept.comap f d) :=
  rfl

-- ══════════════════════════════════════════════════════
-- 2. THE EXTENSION FUNCTOR
-- ══════════════════════════════════════════════════════

/-- Taking extensions is monotone: the concept order is *defined* by what
    extension does. -/
theorem Koncept.extension_mono :
    Monotone (Koncept.extension (α := α)) :=
  fun _ _ h _ ha => h _ ha

/-- The forgetful functor from concepts to sets of entities (both viewed as
    thin categories). Forgets χ; keeps membership. The FCA bridge factors
    through this functor. -/
def Koncept.extensionFunctor : Koncept α ⥤ Set α :=
  (Koncept.extension_mono (α := α)).functor

/-- Extension reflects the order as well as preserving it — but it is NOT
    injective on objects (`preorder_not_partial_order` exhibits two distinct
    concepts with the same extension). The functor is full and faithful
    (automatically, between thin categories) yet not injective on objects:
    concepts carry strictly more structure than their extensions, and that
    extra structure is exactly χ. -/
theorem Koncept.extension_le_iff {c d : Koncept α} :
    c.extension ⊆ d.extension ↔ c ≤ d :=
  Iff.rfl

-- ══════════════════════════════════════════════════════
-- 3. TRANSPORT: CONTRAST-GROUNDING PULLS BACK
-- ══════════════════════════════════════════════════════

/-- CCD witnesses pull back along a change of universe. If the concept `k`
    over `β` is contrast-grounded and the three witnessing entities are
    visible through `f` (have preimages, distinct where required), then
    `comap f k` is contrast-grounded over `α` — by the *same* depths, gaps,
    and similarity, since the pulled-back χ is `k.χ ∘ f`. -/
def CCDWitness₃.comap (f : α → β) (w : CCDWitness₃ β)
    (a b c : α)
    (ha : f a = w.a) (hb : f b = w.b) (hc : f c = w.contrast)
    (hab : a ≠ b) : CCDWitness₃ α where
  k        := Koncept.comap f w.k
  a        := a
  b        := b
  contrast := c
  ha       := by show w.k.pred (f a); rw [ha]; exact w.ha
  hb       := by show w.k.pred (f b); rw [hb]; exact w.hb
  hc       := by show ¬w.k.pred (f c); rw [hc]; exact w.hc
  hab      := hab
  similar  := by
    show SimilarByContrast (w.k.χ (f a)) (w.k.χ (f b)) (w.k.χ (f c))
    rw [ha, hb, hc]
    exact w.similar

/-- The essentiality raise pulls back too: if a definition's raise holds at
    `f a` over `β`, it holds at `a` for the pulled-back genus/differentia.
    Change of universe cannot destroy (or manufacture) essentiality. -/
theorem KonceptDef.raise_comap (f : α → β) (d : KonceptDef β) (a : α)
    (hmem : d.definiendum.pred (f a)) :
    Raise ((Koncept.comap f d.genus).χ a) ((Koncept.comap f d.differentia).χ a) :=
  d.isEssential (f a) hmem
