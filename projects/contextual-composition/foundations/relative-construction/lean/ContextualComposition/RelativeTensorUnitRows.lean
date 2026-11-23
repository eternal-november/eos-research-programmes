module
public import ContextualComposition.RelativeTensorUnitModule

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u
variable {B : Type u} [Category.{v} B]

private theorem action_ext {C D : Type*} [Bicategory C] [Bicategory D] (F G : C ⥤ᵖ D)
    (p : F.toPrelaxFunctor.toPrelaxFunctorStruct.toPrefunctor = G.toPrelaxFunctor.toPrelaxFunctorStruct.toPrefunctor)
    (m : HEq (@F.map₂) (@G.map₂)) (one : HEq F.mapId G.mapId) (two : HEq (@F.mapComp) (@G.mapComp)) : F = G := by
  cases F with
  | mk F fi fc =>
    cases G with
    | mk G gi gc =>
      cases F with
      | mk F _ _ =>
        cases G with
        | mk G _ _ =>
          cases F; cases G; cases p; cases m; cases one; cases two; rfl

/-- The entire row of the hom bimodule is the covariant representable, including its weak structural cells. -/
theorem unitModule_row (a : B) : row (unitModule B) a = LeftUnit.represented a := by
  apply action_ext
  · rfl
  · apply heq_of_eq
    funext i j f g η
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq
  · apply heq_of_eq
    funext i
    apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq
  · apply heq_of_eq
    funext i j k f g
    apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; apply Discrete.hom_eq

theorem unitModule_precompose_obj {a b : B} (u : a ⟶ b) (j : B) (p : Discrete (b ⟶ j)) :
    ((Middle.change (unitModule B) u.op.toLoc).app ⟨j⟩).toFunctor.obj p = Discrete.mk (u ≫ p.as) := rfl

end ContextualComposition.RelativeTensor.Iterated
