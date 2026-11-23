module
public import ContextualComposition.RelativeTensorThreeStep
public import ContextualComposition.RelativeTensorFourBalanceB
public import ContextualComposition.RelativeTensorPentagonOuterBalance

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})


/-- Each port of the final row whiskering is the equality transport at its actual vertex. -/
theorem whisker_port {a b : B} (u : a ⟶ b) (z : (rightInner (middleComposite M N) Y).obj ⟨op b⟩) :
    ∃ h, (Second.port (OuterRow.whisker M N Y) u z).hom = eqToHom h :=
  ⟨Functor.congr_obj (OuterRow.direct_naturality M N Y u.op.toLoc) z, eqToHom_app (OuterRow.direct_naturality M N Y u.op.toLoc) z⟩

end ContextualComposition.RelativeTensor.Iterated
