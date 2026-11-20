module
public import ContextualComposition.AmbientIsoRecognition
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
theorem actualL : AmbientStageReassembly.Frame X (M S (obj S 2 X) m ≫ K S (M S X m)) (lhs (tensor m) (tensor m)) := disjointLeft S X m
theorem actualR : AmbientStageReassembly.Frame X (K S (K S (M S X m)) ≫ M S (obj S 1 X) m) (rhs (tensor m) (tensor m)) := disjointRight S X m
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
