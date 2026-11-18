module
public import ContextualComposition.CutBoundary
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CutFold
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation BoundaryPaste WholeEvaluator TripleBoundary
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m : Nat)
theorem cutSuffix : pairTag S Y n m ⋙ dropInner S Y = suffix S Y n m ⋙ innerInc S Y n m ⋙ endTag S Y n := by
  apply fold_ext (whole S).dest (one S Y)
  · calc
      _ = pairTag S Y n m ⋙ movingFront S Y := congrArg (pairTag S Y n m ⋙ ·) (fold_grade ..)
      _ = fixedFront S Y n m ⋙ (tag (power S) n).functor := cutFront S Y n m
      _ = _ := (congrArg (· ⋙ (tag (power S) n).functor) (suffix_grade S Y n m)).symm.trans
        (congrArg (fun F => suffix S Y n m ⋙ innerInc S Y n m ⋙ F) (SpanPayload.total_projection (one S Y) (tag (power S) n).functor _ (tag (power S) n).dest)).symm
  · calc
      _ = pairTag S Y n m ⋙ movingTail S Y ⋙ evaluate S Y := congrArg (pairTag S Y n m ⋙ ·) (fold_suffix ..)
      _ = fixedTail S Y n m ⋙ branch S Y m := by rw [← Functor.assoc,cutTail,Functor.assoc,WholeEvaluator.tagged]
      _ = _ := (congrArg (· ⋙ ChainPayload.fibreMap (PackedFree.inc S Y m) (𝟭 B)) (suffix_boundary S Y n m)).symm.trans
        ((congrArg (suffix S Y n m ⋙ ·) (leafMap (PackedFree.inc S Y m) (power S n).dest)).symm.trans
        (congrArg (fun F => suffix S Y n m ⋙ innerInc S Y n m ⋙ F) (NativeTrace.leaf_total (one S Y) (tag (power S) n).functor _ (tag (power S) n).dest)).symm)
end ContextualComposition.GrothendieckStep.CutFold
