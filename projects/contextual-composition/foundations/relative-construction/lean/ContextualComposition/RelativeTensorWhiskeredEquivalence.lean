module
public import ContextualComposition.RelativeTensorOuterAssociator

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
set_option backward.isDefEq.respectTransparency false

/-- Whisker an adjoint equivalence of weak covariant actions through the retained quotient. -/
noncomputable def whiskerFirst {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    (E : Bicategory.Equivalence F F') (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}) :
    Tensor F G ≌ Tensor F' G :=
  CategoryTheory.Equivalence.mk (mapFirst E.hom) (mapFirst E.inv)
    (eqToIso (First.map_identity (F := F) (G := G)).symm ≪≫
      (First.homAction F F G).mapIso E.unit ≪≫ eqToIso (First.map_composite E.hom E.inv))
    (eqToIso (First.map_composite (G := G) E.inv E.hom).symm ≪≫
      (First.homAction F' F' G).mapIso E.counit ≪≫ eqToIso (First.map_identity (F := F') (G := G)))

/-- Whisker an adjoint equivalence of weak contravariant actions through the retained quotient. -/
noncomputable def whiskerSecond (F : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
    {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (E : Bicategory.Equivalence G G') :
    Tensor F G ≌ Tensor F G' :=
  CategoryTheory.Equivalence.mk (mapSecond E.hom) (mapSecond E.inv)
    (eqToIso (Second.map_identity (F := F) (G := G)).symm ≪≫
      (Second.homAction F G G).mapIso E.unit ≪≫ eqToIso (Second.map_composite E.hom E.inv))
    (eqToIso (Second.map_composite (F := F) E.inv E.hom).symm ≪≫
      (Second.homAction F G' G').mapIso E.counit ≪≫ eqToIso (Second.map_identity (F := F) (G := G')))

section Four
universe vC uC vD uD vM uM vN uN
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

noncomputable def firstPentagonEquivalence : farLeft X M N Y ≌ innerLeft X M N Y :=
  whiskerFirst (outerEquivalence X M N) Y

theorem firstPentagon_functor : (firstPentagonEquivalence X M N Y).functor = firstPentagonEdge X M N Y := rfl

noncomputable def firstTwoEdges : farLeft X M N Y ≌ innerRight X M N Y :=
  (firstPentagonEquivalence X M N Y).trans (associator X (middleComposite M N) Y)

end Four
end ContextualComposition.RelativeTensor.Iterated
