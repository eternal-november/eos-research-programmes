module
public import ContextualComposition.TaggedSourceCorner
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked NativeCleavage MovingCoordinates MovingCell ProjectedCharts WholeEvaluator
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev outerBase := FibreTotal.projection Y (TripleBoundary.L (U S) (U S) (U S)).dest (TripleBoundary.L (U S) (U S) (U S)).source
theorem dropBase : dropLast S Y ⋙ base S (one S Y) = outerBase S Y :=
  congrArg (· ⋙ (pairSpan S).source) (BoundaryPaste.fold_grade Y (pairSpan S).dest (U S).source (U S).dest (one S Y) (evaluate S Y) (WholeEvaluator.over S Y))
theorem firstBase (F : X S (one S Y) ⥤ Total (three S Y) (𝟭 B)) (h : F ⋙ gradeProjection = base S (one S Y)) :
    (dropLast S Y ⋙ F) ⋙ gradeProjection = outerBase S Y :=
  (congrArg (dropLast S Y ⋙ ·) h).trans (dropBase S Y)
theorem lastBase (F : X S Y ⥤ Total (ChartRealization.twice S Y) (𝟭 B)) (h : F ⋙ proj S Y = base S Y) :
    (regrouping S Y ⋙ foldUnder S Y F h ⋙ outer S Y) ⋙ gradeProjection = outerBase S Y :=
  (congrArg (fun H => regrouping S Y ⋙ foldUnder S Y F h ⋙ H) (WholeEvaluator.over S (ChartRealization.twice S Y))).trans
  ((congrArg (fun H => regrouping S Y ⋙ H ⋙ (U S).source) (BoundaryPaste.fold_grade Y (U S).dest (pairSpan S).source (pairSpan S).dest (ChartRealization.twice S Y) F h)).trans (Lift.over (TripleBoundary.regroup (U S) (U S) (U S)) Y))
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
