module
public import ContextualComposition.RelativeTensorPentagonObjects
public import ContextualComposition.RelativeTensorOuterWhisker

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

/-- The last row reassociation is a pseudonatural adjoint equivalence. -/
noncomputable def rightPentagonRows : Bicategory.Equivalence (rightInner (middleComposite M N) Y) (rightInner M (rightInner N Y)) := by
  letI (b : LocallyDiscrete Bᵒᵖ) : ((OuterRow.whisker M N Y).app b).toFunctor.IsEquivalence := by
    rw [OuterRow.whisker_component]
    exact (rightRowAssociator M N Y b).isEquivalence_functor
  exact PseudonaturalInverse.equivalence (OuterRow.whisker M N Y)

/-- The three-step route through both inner bracketings of the fourfold relative tensor. -/
noncomputable def threeStep : farLeft X M N Y ≌ farRight X M N Y :=
  (firstTwoEdges X M N Y).trans (whiskerSecond X (rightPentagonRows M N Y))

theorem threeStep_functor : (threeStep X M N Y).functor = routeWith X M N Y (OuterRow.whisker M N Y) := rfl

end ContextualComposition.RelativeTensor.Iterated
