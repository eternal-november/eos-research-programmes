module
public import ContextualComposition.AmbientFlatTerminal
public import ContextualComposition.AmbientPackedStages
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientStageReassembly
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadDisjointCut AmbientBicategory AmbientCoordinates
open AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientExchangeDemand AmbientFlatTerminal AmbientDisjointFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
open ContextadModification AmbientPackedTips AmbientNativeTerminal ContextadWeakWeight
variable (f g : Map S 2 1) (pg : gradeCart g)
variable {a b : obj S 4 X ⟶ obj S 2 X}
def Frame (z : obj S 4 X ⟶ obj S 2 X) (r : Map S 4 2) : Prop := encode S z = raw (underlying X) r
abbrev nestedMate (x : Raw S X 4) := (AmbientComparisonRead.q S f (oper S g pg X)).app ((I (S := S) X).obj x)
variable (ht : ∀ x, Aligned ((leafAt (underlying (obj S 1 X)) (power S 1).dest).map (nestedMate X f g pg x))
  ((chart S X 1).map ((AmbientChosenTail.finalOne (S := S) X).map (native X f g pg x))))
include ht in
theorem readDiagram (t : a ⟶ b)
    (ea : Frame X a (lhs f g))
    (eb : Frame X b (rhs f g))
    (h : ∀ y, Aligned (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) (f := a) (g := b) S t y)
      ((AmbientComparisonRead.q S f (oper S g pg X)).app y)) :
    AmbientHorizontalRead.Reads (X := X) (j := 4) (k := 2) t (disjoint f g pg) := by
  intro x
  let q := (AmbientChartRows.readNested X t x).trans (h _)
  exact rowsTwo X _ (native X f g pg x) (Functor.congr_obj ea x) (Functor.congr_obj eb x)
    (AmbientMateCalculus.pureOfAligned (q.map gradeProjection) (weakGrade _ _ f.grade f.leg (oper S g pg X).hom _))
    (AmbientNativeTerminal.head X f g pg x)
    ((q.map (leafAt (underlying (obj S 1 X)) (power S 1).dest)).trans (ht x))
end
end ContextualComposition.GrothendieckStep.AmbientStageReassembly
