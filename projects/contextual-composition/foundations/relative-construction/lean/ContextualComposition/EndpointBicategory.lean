module
public import ContextualComposition.WeakChoiceCoherence
public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Groupoid

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe vK vL vK' vL' vC uK uL uK' uL' uC
variable {C : Type uC} [Category.{vC} C] {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

def ChoiceIso.symm {T U : Data e d e' d'} (a : ChoiceIso T U) : ChoiceIso U T :=
  ⟨a.input.symm, a.output.symm, a.input_inv, a.output_inv⟩

instance dataGroupoid : Groupoid (Data e d e' d') where
  Hom := ChoiceIso
  id := ChoiceIso.refl
  comp := ChoiceIso.trans
  id_comp a := by apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x <;> exact Category.id_comp _
  comp_id a := by apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x <;> exact Category.comp_id _
  assoc a b c := by apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x <;> exact Category.assoc _ _ _
  inv := ChoiceIso.symm
  inv_comp a := by
    apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x
    · exact a.input.inv_hom_id_app x
    · exact a.output.inv_hom_id_app x
  comp_inv a := by
    apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x
    · exact a.input.hom_inv_id_app x
    · exact a.output.hom_inv_id_app x

/-- An input and output presentation with their common base fixed. The universes of the grade categories may differ. -/
structure Presentation (C : Type uC) [Category.{vC} C] where
  input : Type uK
  output : Type uL
  [inputCategory : Category.{vK} input]
  [outputCategory : Category.{vL} output]
  source : input ⥤ C
  target : output ⥤ C

attribute [instance] Presentation.inputCategory Presentation.outputCategory

namespace Presentation
abbrev Transport (A B : Presentation.{vK,vL,vC,uK,uL,uC} C) := Data A.source A.target B.source B.target

instance arrows : CategoryStruct (Presentation.{vK,vL,vC,uK,uL,uC} C) where
  Hom := Transport
  id A := identityData A.source A.target
  comp T U := composeData T U

def choiceToIso {T U : Data e d e' d'} (h : ChoiceIso T U) : T ≅ U where
  hom := h
  inv := h.symm
  hom_inv_id := Groupoid.comp_inv _
  inv_hom_id := Groupoid.inv_comp _

local macro "component_ext" : tactic =>
  `(tactic| apply ChoiceIso.ext <;> apply Iso.ext <;> apply NatTrans.ext <;> funext x)

/-- The two-cells compare endpoint lifts by compatible isomorphisms. The one-cells retain possibly noninvertible input and output lift arrows. -/
instance bicategory : Bicategory (Presentation.{vK,vL,vC,uK,uL,uC} C) where
  homCategory _ _ := dataGroupoid.toCategory
  whiskerLeft := ChoiceIso.whiskerLeft
  whiskerRight := ChoiceIso.whiskerRight
  associator f g h := choiceToIso (associatorChoice f g h)
  leftUnitor f := choiceToIso (leftUnitChoice f)
  rightUnitor f := choiceToIso (rightUnitChoice f)
  whiskerLeft_id _ _ := by component_ext <;> rfl
  whiskerLeft_comp := by intros; component_ext <;> rfl
  id_whiskerLeft η := by component_ext <;> change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  comp_whiskerLeft := by intros; component_ext <;> change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  id_whiskerRight _ g := by
    component_ext
    · exact g.input.map_id _
    · exact g.output.map_id _
  comp_whiskerRight η θ i := by
    component_ext
    · exact i.input.map_comp _ _
    · exact i.output.map_comp _ _
  whiskerRight_id η := by component_ext <;> change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  whiskerRight_comp η _ _ := by component_ext <;> change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  whisker_assoc := by intros; component_ext <;> change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;> erw [Category.id_comp, Category.comp_id] <;> rfl
  whisker_exchange η θ := (ChoiceIso.horizontal_interchange η θ).symm
  pentagon f g h i := (choice_pentagon f g h i).symm
  triangle f g := choice_triangle f g

end Presentation
end ContextualComposition.Factorization.Endpoint
