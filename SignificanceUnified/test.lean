import Lean
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import ProofWidgets.Component.Panel.SelectionPanel  -- registers goalsLocationsToExprs RPC
open Lean Widget

@[widget_module]
def helloWidget : Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = (props && props.name) || 'world';
      return React.createElement('p', {}, 'Hello ' + name + '!');
    }
  "

-- Place cursor here to see the widget in the infoview
#widget helloWidget

-- ═══════════════════════════════════════════════════════
-- Commutative diagram: place cursor on `sorry` to see the diagram
-- ═══════════════════════════════════════════════════════
universe u
open ProofWidgets CategoryTheory

local instance : Category (Type u) where
  Hom α β := α → β
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Triangle: place cursor on the `skip` line to see the diagram (goal: f ≫ g = h). -/
example {X Y Z : Type} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) :
    True → f ≫ g = h := by
  with_panel_widgets [GoalTypePanel]
  intro _
  skip  -- cursor here: goal still present
  sorry

/-- Square: place cursor on the `skip` line to see the diagram (goal: f ≫ g = i ≫ j). -/
example {X Y Z : Type} {f i : X ⟶ Y} {g j : Y ⟶ Z} {h : X ⟶ Z} :
    h = f ≫ g → i ≫ j = h → f ≫ g = i ≫ j := by
  with_panel_widgets [GoalTypePanel]
  intro h₁ h₂
  skip  -- cursor here: goal still present
  sorry