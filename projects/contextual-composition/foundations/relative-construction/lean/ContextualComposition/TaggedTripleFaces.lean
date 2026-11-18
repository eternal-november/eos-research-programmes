module
public import ContextualComposition.WholeEvaluator
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked TripleBoundary MovingCoordinates MovingCell ProjectedCharts FibreEndpoints WholeEvaluator
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev U := whole S
abbrev input := Total Y (TripleBoundary.L (U S) (U S) (U S)).dest
abbrev three := ChartRealization.twice S (one S Y)
noncomputable abbrev dropLast := lastPair (U S) (U S) (U S) Y (one S Y) (evaluate S Y) (WholeEvaluator.over S Y)
abbrev regrouping := Lift.total (regroup (U S) (U S) (U S)) Y
noncomputable abbrev firstLeft := dropLast S Y ⋙ leftTotal S (one S Y)
noncomputable abbrev firstRight := dropLast S Y ⋙ rightTotal S (one S Y)
noncomputable def first := isoWhiskerLeft (dropLast S Y) (cell S (one S Y))
noncomputable abbrev foldUnder (F : X S Y ⥤ Total (ChartRealization.twice S Y) (𝟭 B)) (h : F ⋙ proj S Y = base S Y) :=
  BoundaryPaste.fold Y (U S).dest (pairSpan S).source (pairSpan S).dest (ChartRealization.twice S Y) F h
noncomputable abbrev outer := evaluate S (ChartRealization.twice S Y)
noncomputable abbrev lastLeft := regrouping S Y ⋙ foldUnder S Y (leftTotal S Y) (leftOver S Y) ⋙ outer S Y
noncomputable abbrev lastRight := regrouping S Y ⋙ foldUnder S Y (rightTotal S Y) (rightOver S Y) ⋙ outer S Y
noncomputable def last := isoWhiskerLeft (regrouping S Y) (isoWhiskerRight
  (SuffixCell.foldIsoCell Y (ChartRealization.twice S Y) (U S).dest (pairSpan S).source (pairSpan S).dest
    (leftOver S Y) (rightOver S Y) (cell S Y) (totalVertical S Y)) (outer S Y))
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
