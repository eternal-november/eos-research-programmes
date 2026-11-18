module
public import ContextualComposition.FibreEndpoints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.EndpointValues
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates MovingCell ProjectedCharts FibreReader FibreEndpoints
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (a : B)
abbrev into := FibreTotal.into Y (pairSpan S).dest (pairSpan S).source a
noncomputable abbrev strictF (F : X S Y ⥤ Total (twice S Y) (𝟭 B)) (h : F ⋙ proj S Y = base S Y) :=
  into S Y a ⋙ SpanPayload.fibreFunctor F (proj S Y) h a
noncomputable abbrev restrictValue (F : X S Y ⥤ Total (twice S Y) (𝟭 B)) (h : F ⋙ proj S Y = base S Y) :=
  strictF S Y a F h ⋙ FibreValue.value (twice S Y) a
theorem decode (F : X S Y ⥤ Total (twice S Y) (𝟭 B)) (h : F ⋙ proj S Y = base S Y) (V : W S Y a ⥤ (twice S Y).obj (op a))
    (k : inp S Y a ⋙ F = off S Y a ⋙ V ⋙ eff S Y a) : restrictValue S Y a F h = V := by
  have e : strictF S Y a F h = V ⋙ FibreValue.embed (twice S Y) a := by
    apply EvalPayload.cancelInclusion
    exact (congrArg (into S Y a ⋙ ·) (SpanPayload.fibre_diagram F (proj S Y) h a)).trans (congrArg (into S Y a ⋙ ·) k)
  exact (congrArg (· ⋙ FibreValue.value (twice S Y) a) e).trans (congrArg (V ⋙ ·) (FibreValue.embed_value (twice S Y) a))
theorem left : restrictValue S Y a (leftTotal S Y) (leftOver S Y) = stages S Y a :=
  decode S Y a _ (leftOver S Y) _ (leftRestrict S Y a)
theorem right : restrictValue S Y a (rightTotal S Y) (rightOver S Y) = previous S Y a :=
  decode S Y a _ (rightOver S Y) _ (rightRestrict S Y a)
end ContextualComposition.GrothendieckStep.EndpointValues
