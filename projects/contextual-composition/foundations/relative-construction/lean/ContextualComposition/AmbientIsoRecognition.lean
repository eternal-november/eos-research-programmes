module
public import ContextualComposition.AmbientSquareRecognition
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
variable (f g : Map S 2 1) (p : gradeCart g)
variable {a b : obj S 2 (obj S 2 X) ⟶ obj S 1 (obj S 1 X)}
theorem fromIso (s : a ≅ b) (l : AmbientStageReassembly.Frame X b (lhs f g)) (r : AmbientStageReassembly.Frame X a (rhs f g))
    (h : AmbientBoundaryReduction.RRead (i := 2) (j := 1) S (oper S g p X) s f) : Reading X f g p s.inv :=
  nestedRow (a := b) (b := a) X f g p s.inv l r h
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
