module
public import ContextualComposition.AmbientBoundRow
public import ContextualComposition.AmbientCertifiedRow
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFourToTwo
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadDisjointCut AmbientBicategory AmbientCoordinates
open AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientExchangeDemand AmbientFlatTerminal AmbientDisjointFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
open ContextadModification AmbientPackedTips AmbientNativeTerminal ContextadWeakWeight
theorem exchange : Law X m := conclude (d := Law X m) X (tensor m) (tensor m) (interchange X m).hom
  (flatPoints X m) (AmbientExchangeChecklist.actual X m)
set_option linter.defProp false in
def row := (AmbientExchangeChecklist.actual X m).mp (exchange X m)
set_option linter.defProp false in
def whisker := whiskered X m (exchange X m)
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
