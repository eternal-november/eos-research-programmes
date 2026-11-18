module
public import ContextualComposition.CutReadout
public import ContextualComposition.TaggedStageVertical
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked MovingCoordinates MovingCell ProjectedCharts WholeEvaluator CutReadout
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
noncomputable def prefixToStages := isoWhiskerLeft (dropLast S Y) (bridge S (one S Y))
noncomputable def suffixToStages := isoWhiskerLeft (regrouping S Y) (isoWhiskerRight
  (SuffixCell.foldIsoCell Y (ChartRealization.twice S Y) (U S).dest (pairSpan S).source (pairSpan S).dest
    (leftOver S Y) (binaryOver S Y) (bridge S Y) (bridgeVertical S Y (readout S Y))) (outer S Y))
noncomputable def sourceCorner := prefixToStages S Y ≪≫ eqToIso (ordinary S Y) ≪≫ (suffixToStages S Y).symm
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
