module
public import ContextualComposition.AmbientDisjointRecognition
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
section Flat
variable {a b : obj S 4 X ⟶ obj S 2 X}
def Reading (t : a ⟶ b) : Prop := AmbientHorizontalRead.Reads (X := X) (j := 4) (k := 2) t (disjoint f g p)
def Nested (t : a ⟶ b) : Prop := ∀ y, Aligned (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) (f := a) (g := b) S t y) ((AmbientComparisonRead.q S f (oper S g p X)).app y)
theorem named (t : a ⟶ b) (l : AmbientStageReassembly.Frame X a (lhs f g)) (r : AmbientStageReassembly.Frame X b (rhs f g)) (h : Nested X f g p t) : Reading X f g p t :=
  recognize (a := a) (b := b) X f g p t l r h
end Flat
section Arbitrary
variable {a b : obj S 2 (obj S 2 X) ⟶ obj S 1 (obj S 1 X)}
theorem nestedRow (t : a ⟶ b) (l : AmbientStageReassembly.Frame X a (lhs f g)) (r : AmbientStageReassembly.Frame X b (rhs f g)) (h : Nested X f g p t) : Reading X f g p t :=
  named (a := a) (b := b) X f g p t l r h
end Arbitrary
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
