module
public import ContextualComposition.AmbientActualIso
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
variable (f g : Map S 2 1) (pg : gradeCart g)
variable {a b : obj S 4 X ⟶ obj S 2 X}
set_option linter.defProp false in
def testsOf (t : a ⟶ b) (l : AmbientStageReassembly.Frame X a (lhs f g)) (r : AmbientStageReassembly.Frame X b (rhs f g))
    (h : Reading X f g pg t) := (AmbientExchangeChecklist.observed X f g pg t l r).mp h
set_option linter.defProp false in
def currentRow := testsOf X (tensor m) (tensor m) m.cart (squareM S m (M S X m)).inv (actualL X m) (actualR X m) (current X m)
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
