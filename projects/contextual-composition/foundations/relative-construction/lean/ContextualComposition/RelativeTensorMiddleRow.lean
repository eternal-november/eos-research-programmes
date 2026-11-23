module
public import ContextualComposition.RelativeTensorFourFactors

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (b : B)

theorem middleRow_pre : (row (middleComposite M N) b).toPrelaxFunctor = (leftInner (row M b) N).toPrelaxFunctor := rfl

theorem middleRow_unit (d : LocallyDiscrete D) :
    (row (middleComposite M N) b).mapId d = (leftInner (row M b) N).mapId d := by
  apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
  change ((_ ≫ 𝟙 _) ≫ 𝟙 _) = _
  rw [Category.comp_id,Category.comp_id]
  rfl

theorem middleRow_comp {d d' d'' : LocallyDiscrete D} (f : d ⟶ d') (g : d' ⟶ d'') :
    (row (middleComposite M N) b).mapComp f g = (leftInner (row M b) N).mapComp f g := by
  apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
  change ((_ ≫ 𝟙 _) ≫ 𝟙 _) = _
  rw [Category.comp_id,Category.comp_id]
  rfl

private theorem action_eq {T U : Type*} [Bicategory T] [Bicategory U] (F G : T ⥤ᵖ U)
    (h : F.toPrelaxFunctor = G.toPrelaxFunctor)
    (hi : HEq F.mapId G.mapId) (hc : HEq (@F.mapComp) (@G.mapComp)) : F = G := by
  cases F; cases G; cases h; cases hi; cases hc; rfl

/-- Evaluation of the substituted middle action at a fixed first endpoint
recovers the full left-inner pseudofunctor, including both structure isomorphisms. -/
theorem middleRow : row (middleComposite M N) b = leftInner (row M b) N := by
  apply action_eq _ _ (middleRow_pre M N b)
  · exact heq_of_eq (funext (middleRow_unit M N b))
  · apply heq_of_eq
    funext d d' d'' f g
    exact middleRow_comp M N b f g

end ContextualComposition.RelativeTensor.Iterated
