module
public import ContextualComposition.RelativeTensorOuterRowArrow

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

theorem columnPacked {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (d : D) (p : Tensor (row M a.as.unop) (column N d)) :
    pack (((rowId M N c).app ⟨d⟩).toFunctor.map ((((middleComposite M N).obj ⟨d⟩).mapComp u v).hom.toNatTrans.app p)) =
      pack (((firstMapCell (Middle.changeComposition M u v).hom N).as.app ⟨d⟩).toNatTrans.app (((rowId M N a).app ⟨d⟩).toFunctor.obj p)) :=
  congrArg pack (columnComp M N u v d p)

/-- Specialize the typed-arrow compositor to the actual row identification. Its endpoints, as well as the coefficient arrow, are retained. -/
theorem normalizedCompositor {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) (z : source M N Y a) :
    pack ((mapFirst (G := Y) (rowId M N c)).map (((rightInner (middleComposite M N) Y).mapComp u v).hom.toNatTrans.app z)) =
      pack ((First.mapCell (G := Y) (firstMapCell (Middle.changeComposition M u v).hom N).as).app ((mapFirst (G := Y) (rowId M N a)).obj z)) :=
  normalize_from_columns Y (middleComposite M N) u v (rowId M N a) (rowId M N c)
    (firstMapCell (Middle.changeComposition M u v).hom N) (columnPacked M N u v) z

end ContextualComposition.RelativeTensor.Iterated.OuterRow
