module
public import ContextualComposition.AmbientExposeReading
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
variable (f g : Map S 2 1) (pg : gradeCart g)
variable {a b : obj S 4 X ⟶ obj S 2 X} (t : a ⟶ b)
def Point (x : Raw S X 4) : Prop := AmbientExchangeChecklist.Row X f g (grade (underlying X) (power S 4).dest x) (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x)
theorem obtainRows (l : AmbientStageReassembly.Frame X a (lhs f g)) (r : AmbientStageReassembly.Frame X b (rhs f g))
    (h : Reading X f g pg t) : ∀ x, Point X f g t x := testsOf X f g pg t l r h
theorem conclude (h : ∀ x, Point X f g t x) {d : Prop}
    (w : d ↔ ∀ x, AmbientExchangeChecklist.Row X f g (grade (underlying X) (power S 4).dest x) (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x)) : d := w.mpr h
set_option linter.defProp false in
def flatPoints := obtainRows X (tensor m) (tensor m) m.cart (squareM S m (M S X m)).inv (actualL X m) (actualR X m) (current X m)
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
