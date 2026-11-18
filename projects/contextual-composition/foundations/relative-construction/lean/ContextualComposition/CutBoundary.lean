module
public import ContextualComposition.WholeEvaluator
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CutFold
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation BoundaryPaste WholeEvaluator TripleBoundary
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m : Nat)
noncomputable abbrev dropInner := lastOne (whole S) (whole S) Y (one S Y) (evaluate S Y) (WholeEvaluator.over S Y)
abbrev pairTag := Lift.total (NativePacked.tagged S (n,m)) Y
abbrev endTag := Lift.total (tag (power S) n) (one S Y)
abbrev innerInc := ChainPayload.fibreMap (PackedFree.inc S Y m) (power S n).dest
abbrev fixedTail := tail Y (power S n).dest (power S m).source (power S m).dest
abbrev movingTail := tail Y (whole S).dest (whole S).source (whole S).dest
abbrev fixedFront := front Y (power S n).dest (power S m).source (power S m).dest
abbrev movingFront := front Y (whole S).dest (whole S).source (whole S).dest
theorem cutFront : pairTag S Y n m ⋙ movingFront S Y = fixedFront S Y n m ⋙ (tag (power S) n).functor := by
  exact congrArg (· ⋙ Strict.fst (whole S).dest (whole S).source) (SpanPayload.total_projection Y (NativePacked.tagged S (n,m)).functor _ (NativePacked.tagged S (n,m)).dest)
theorem cutTail : pairTag S Y n m ⋙ movingTail S Y = fixedTail S Y n m ⋙ Lift.total (tag (power S) m) Y := by
  exact (SpanPayload.total_comp Y (NativePacked.tagged S (n,m)).functor _ (NativePacked.tagged S (n,m)).dest (Strict.snd (whole S).dest (whole S).source) _ rfl).trans
    (SpanPayload.total_comp Y (Strict.snd (power S n).dest (power S m).source) _ rfl (tag (power S) m).functor _ (tag (power S) m).dest).symm
theorem leafMap {Z G : WordTrace.Pr (B := B)} (t : Z ⟶ G) {K : Type*} [Category* K] (e : K ⥤ B) :
    ChainPayload.fibreMap t e ⋙ NativeTrace.leaf G e = NativeTrace.leaf Z e ⋙ ChainPayload.fibreMap t (𝟭 B) := rfl
end ContextualComposition.GrothendieckStep.CutFold
