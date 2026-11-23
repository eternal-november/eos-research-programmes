module
public import ContextualComposition.RelativeTensorOuterRowCoherence
public import ContextualComposition.RelativeTensorRowStrongSquares

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Reassociation as a strong comparison of the actual contravariant first-index diagrams. -/
def whisker : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y) :=
  strongOfSquares (rightInner (middleComposite M N) Y) (rightInner M (rightInner N Y))
    (direct M N Y) (direct_naturality M N Y) (fun a z => congrArg pack (direct_unit M N Y a z)) (direct_comp_packed M N Y)

theorem whisker_component (b : LocallyDiscrete Bᵒᵖ) :
    ((whisker M N Y).app b).toFunctor = (rightRowAssociator M N Y b).functor :=
  (direct_eq M N Y b).trans (component_eq M N Y b)

universe vX uX
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})

/-- The resulting outer-B whisker between the actual four-factor quotient categories. -/
def outerWhisker : innerRight X M N Y ⥤ farRight X M N Y := mapSecond (F := X) (whisker M N Y)

end ContextualComposition.RelativeTensor.Iterated.OuterRow
