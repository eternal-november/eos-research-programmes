module
public import ContextualComposition.TaggedSquareRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeRegroupChart
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked TripleBoundary NativeAssoc.Three
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
abbrev rightSpan := mapProduct (tag (power S) n) (NativePacked.tagged S (m,k))
abbrev rightIncl := Lift.total (rightSpan S n m k) Y
theorem regroupTag : (TaggedTripleCover.spanTag S n m k).functor ⋙ (regroup (whole S) (whole S) (whole S)).functor =
    (regroup (power S n) (power S m) (power S k)).functor ⋙ (rightSpan S n m k).functor := by
  apply Functor.ext (fun _ => rfl)
theorem totalRegroup : TaggedTripleCover.incl S Y n m k ⋙ TaggedTripleFaces.regrouping S Y =
    TripleEvaluation.rebracket S Y n m k ⋙ rightIncl S Y n m k := by
  exact (SpanPayload.total_comp Y (TaggedTripleCover.spanTag S n m k).functor _ (TaggedTripleCover.spanTag S n m k).dest
    (regroup (whole S) (whole S) (whole S)).functor _ (regroup (whole S) (whole S) (whole S)).dest).trans
    ((Lift.total_eq Y (regroupTag S n m k)).trans (SpanPayload.total_comp Y (regroup (power S n) (power S m) (power S k)).functor _
      (regroup (power S n) (power S m) (power S k)).dest (rightSpan S n m k).functor (R (whole S) (whole S) (whole S)).dest (rightSpan S n m k).dest).symm)
end ContextualComposition.GrothendieckStep.NativeRegroupChart
