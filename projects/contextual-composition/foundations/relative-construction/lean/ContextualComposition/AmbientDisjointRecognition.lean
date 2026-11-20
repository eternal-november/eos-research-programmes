module
public import ContextualComposition.AmbientStageReassembly
public import ContextualComposition.AmbientNativeTerminal
public import ContextualComposition.AmbientPackedTips
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
set_option linter.defProp false in
def terminal (x : Raw S X 4) := tailFrom X f g p x (inputTip X f x)
variable {a b : obj S 4 X ⟶ obj S 2 X}
set_option linter.defProp false in
def recognize (t : a ⟶ b) (ea : AmbientStageReassembly.Frame X a (lhs f g)) (eb : AmbientStageReassembly.Frame X b (rhs f g))
    (h : ∀ y, Aligned (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) (f := a) (g := b) S t y)
      ((AmbientComparisonRead.q S f (oper S g p X)).app y)) :=
  AmbientStageReassembly.readDiagram (a := a) (b := b) X f g p (terminal X f g p) t ea eb h
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
