module
public import ContextualComposition.WholeEvaluator
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CutPayload
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation WholeEvaluator ChartRealization
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m : Nat)
theorem globalMap {Y Z : WordTrace.Pr (B := B)} (t : Y ⟶ Z) :
    (n : Nat) → ChainPayload.fibreMap t (power S n).dest ⋙ global S Z n =
      global S Y n ⋙ ChainPayload.fibreMap (ChainPayload.layerMap t S n) (𝟭 B)
  | 0 => rfl
  | n+1 => EvalPayload.nativeSquare t S n
theorem branchMap :
    ChainPayload.fibreMap (PackedFree.inc S Y m) (power S n).dest ⋙ branch S (one S Y) n =
    global S (out S Y m) n ⋙ push S Y (n,m) := by
  exact (congrArg (· ⋙ ChainPayload.fibreMap (PackedFree.inc S (one S Y) n) (𝟭 B)) (globalMap S (PackedFree.inc S Y m) n)).trans
    (congrArg (global S (out S Y m) n ⋙ ·) (ChainPayload.fibreMap_comp _ _ _).symm)
end ContextualComposition.GrothendieckStep.CutPayload
