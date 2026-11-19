module
public import ContextualComposition.JoinedTarget
public import ContextualComposition.TripleStageRead
public import ContextualComposition.FrameRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.JoinedChartFrames
open CategoryTheory CategoryTheory.Functor Opposite TaggedTripleCover TaggedTripleFaces TaggedSquareRecognition FrameRecognition TripleStageRead JoinedTarget TaggedFixedSquare TripleEvaluation
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
theorem joinedFirstRead : incl S Y n m k ⋙ ordinaryLeft S Y = b₀ S Y n m k :=
  (leftStage S Y n m k).trans (congrArg (· ⋙ packOut S Y n m k) (firstFace S Y n m k))
theorem joinedLastRead : incl S Y n m k ⋙ ordinaryRight S Y = d₀ S Y n m k :=
  (rightStage S Y n m k).trans (congrArg (· ⋙ packOut S Y n m k) (lastFace S Y n m k))
noncomputable def stageFirst := frame (incl S Y n m k) (prefixToStages S Y) (leftStage S Y n m k)
noncomputable def joinFirst := frame (incl S Y n m k) (joinedPrefix S Y) (joinedFirstRead S Y n m k)
noncomputable def stageLast := frame (incl S Y n m k) (suffixToStages S Y) (rightStage S Y n m k)
noncomputable def joinLast := frame (incl S Y n m k) (joinedSuffix S Y) (joinedLastRead S Y n m k)
theorem firstTest : edge S Y n m k (first S Y).hom ≫ (joinFirst S Y n m k).hom = (stageFirst S Y n m k).hom ≫ fa S Y n m k := by
  rw [firstCast]
  exact side (incl S Y n m k) _ _ _ (prefixLaw S Y) _ _ _
theorem lastTest : edge S Y n m k (last S Y).hom ≫ (joinLast S Y n m k).hom = (stageLast S Y n m k).hom ≫ fb S Y n m k := by
  rw [lastCast]
  exact side (incl S Y n m k) _ _ _ (suffixLaw S Y) _ _ _
theorem sourceTest : edge S Y n m k (sourceCorner S Y).hom ≫ (stageLast S Y n m k).hom = (stageFirst S Y n m k).hom ≫ fs S Y n m k := by
  rw [sourceCast]
  exact middle (incl S Y n m k) (prefixToStages S Y) (suffixToStages S Y) (ordinary S Y) _ _ _
theorem targetTest : edge S Y n m k (comparison S Y).hom ≫ (joinLast S Y n m k).hom = (joinFirst S Y n m k).hom ≫ ft S Y n m k := by
  rw [targetCast]
  exact middle (incl S Y n m k) (joinedPrefix S Y) (joinedSuffix S Y) (ordinary S Y) _ _ _
theorem byCharts : (first S Y).hom ≫ (comparison S Y).hom = (sourceCorner S Y).hom ≫ (last S Y).hom :=
  onCharts S Y _ _ _ _ (stageFirst S Y) (joinFirst S Y) (stageLast S Y) (joinLast S Y)
    (firstTest S Y) (lastTest S Y) (sourceTest S Y) (targetTest S Y)
theorem unique {t : firstRight S Y ⟶ lastRight S Y}
    (test : ∀ n m k, edge S Y n m k t ≫ (joinLast S Y n m k).hom = (joinFirst S Y n m k).hom ≫ ft S Y n m k) :
    t = (comparison S Y).hom :=
  TaggedChartTest.uniqueChart S Y t _ (joinLast S Y) fun n m k => (test n m k).trans (targetTest S Y n m k).symm
end ContextualComposition.GrothendieckStep.JoinedChartFrames
