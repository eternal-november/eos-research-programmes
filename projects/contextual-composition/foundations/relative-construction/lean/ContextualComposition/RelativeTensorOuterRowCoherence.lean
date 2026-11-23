module
public import ContextualComposition.RelativeTensorOuterRowCompositor

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

private def applyArrow {E F : Type*} [Category* E] [Category* F] (G : E ⥤ F) (p : TypedArrow E) : TypedArrow F :=
  pack (G.map p.arrow)

theorem direct_unit (b : LocallyDiscrete Bᵒᵖ) (z : source M N Y b) :
    (direct M N Y b).map (((rightInner (middleComposite M N) Y).mapId b).hom.toNatTrans.app z) =
      ((rightInner M (rightInner N Y)).mapId b).hom.toNatTrans.app ((direct M N Y b).obj z) :=
  (congrArg (rebracket M N Y b).map (normalize_unit M N Y b z)).trans
    (first_row_unit M N Y b ((mapFirst (G := Y) (rowId M N b)).obj z))

/-- The actual weak compositor square after rebracketing, with both morphism endpoints retained. -/
theorem direct_comp_packed {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (z : source M N Y a) :
    pack ((direct M N Y c).map (((rightInner (middleComposite M N) Y).mapComp u v).hom.toNatTrans.app z)) =
      pack (((rightInner M (rightInner N Y)).mapComp u v).hom.toNatTrans.app ((direct M N Y a).obj z)) :=
  (congrArg (applyArrow (rebracket M N Y c)) (normalizedCompositor M N Y u v z)).trans
    (congrArg pack (first_row_compositor M N Y u v ((mapFirst (G := Y) (rowId M N a)).obj z)))

end ContextualComposition.RelativeTensor.Iterated.OuterRow
