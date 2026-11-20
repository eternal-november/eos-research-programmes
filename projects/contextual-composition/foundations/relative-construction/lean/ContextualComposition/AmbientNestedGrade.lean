module
public import ContextualComposition.AmbientObservationChart
public import ContextualComposition.AmbientExchangeChecklist
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNestedGrade
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts SpanApex
open AmbientHorizontalFrames AmbientHorizontalDiagrams ContextadWeakWeight AmbientBoundaryReduction AmbientObservationChart
open AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
theorem nestedGrade {V W : Obj.{u,v} B} (f : V ⟶ W) (x : Raw S V 2) :
    Pure (gradeMap (atRaw (X := V) (Y := W) (i := 2) (j := 1) S (squareM S m f).inv x)) :=
  AmbientMateCalculus.pureOfAligned ((muRead S f m x).map gradeProjection) (weakGrade _ _ _ _ f.hom x)
end ContextualComposition.GrothendieckStep.AmbientNestedGrade
