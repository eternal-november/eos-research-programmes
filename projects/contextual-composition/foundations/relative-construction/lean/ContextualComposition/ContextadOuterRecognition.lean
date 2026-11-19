module
public import ContextualComposition.ContextadOuterStage
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage BoundaryPaste
open ContextadRoutes ContextadWeakAction TelescopeSquares ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem frontOne (n : Nat) : (blocks S n 1).first = NativeAssoc.front S n := NativeTrace.cut_first S n 0
theorem tailOne (n : Nat) : (blocks S n 1).rest = NativeAssoc.last S n := NativeTrace.cut_tip S n 0
theorem ready0 : stage (S := S) Y (power S 0) = splitAt Y 0 1 := by
  apply fold_ext
  · exact (stageHead (S := S) Y _).trans ((congrArg (gradeProjection (Y := Y) (e := (power S (0+1)).dest) ⋙ ·) (frontOne (S := S) 0).symm).trans (splitFront (S := S) Y 0 1).symm)
  · have t := NativePacked.Lift.total_eq Y (d := right P S) (h := rfl) (k := (blocks S 0 1).dest) (tailOne (S := S) 0).symm
    exact (stageLeaf (S := S) Y _).trans ((congrArg (· ⋙ BlockEvaluation.global S Y 1) t).trans (splitTail (S := S) Y 0 1).symm)
theorem resolve0 : stage (S := S) Y (power S 0) ⋙ BlockEvaluation.global S (LY (S := S) Y) 0 = BlockEvaluation.global S Y (0+1) :=
  (congrArg (· ⋙ BlockEvaluation.global S (LY (S := S) Y) 0) (ready0 (S := S) Y)).trans
    ((splitTransport (S := S) Y 0 1).trans (selfTransport (G := PackedFree.pow S Y (0+1)) (BlockEvaluation.global S Y (0+1)) (PackedCuts.sameLength S Y (0,1)).symm))
theorem ready1 : stage (S := S) Y (power S 1) = splitAt Y 1 1 := by
  apply fold_ext
  · exact (stageHead (S := S) Y _).trans ((congrArg (gradeProjection (Y := Y) (e := (power S (1+1)).dest) ⋙ ·) (frontOne (S := S) 1).symm).trans (splitFront (S := S) Y 1 1).symm)
  · have t := NativePacked.Lift.total_eq Y (d := right P S) (h := rfl) (k := (blocks S 1 1).dest) (tailOne (S := S) 1).symm
    exact (stageLeaf (S := S) Y _).trans ((congrArg (· ⋙ BlockEvaluation.global S Y 1) t).trans (splitTail (S := S) Y 1 1).symm)
theorem resolve1 : stage (S := S) Y (power S 1) ⋙ BlockEvaluation.global S (LY (S := S) Y) 1 = BlockEvaluation.global S Y (1+1) :=
  (congrArg (· ⋙ BlockEvaluation.global S (LY (S := S) Y) 1) (ready1 (S := S) Y)).trans
    ((splitTransport (S := S) Y 1 1).trans (selfTransport (G := PackedFree.pow S Y (1+1)) (BlockEvaluation.global S Y (1+1)) (PackedCuts.sameLength S Y (1,1)).symm))
theorem ready2 : stage (S := S) Y (power S 2) = splitAt Y 2 1 := by
  apply fold_ext
  · exact (stageHead (S := S) Y _).trans ((congrArg (gradeProjection (Y := Y) (e := (power S (2+1)).dest) ⋙ ·) (frontOne (S := S) 2).symm).trans (splitFront (S := S) Y 2 1).symm)
  · have t := NativePacked.Lift.total_eq Y (d := right P S) (h := rfl) (k := (blocks S 2 1).dest) (tailOne (S := S) 2).symm
    exact (stageLeaf (S := S) Y _).trans ((congrArg (· ⋙ BlockEvaluation.global S Y 1) t).trans (splitTail (S := S) Y 2 1).symm)
theorem resolve2 : stage (S := S) Y (power S 2) ⋙ BlockEvaluation.global S (LY (S := S) Y) 2 = BlockEvaluation.global S Y (2+1) :=
  (congrArg (· ⋙ BlockEvaluation.global S (LY (S := S) Y) 2) (ready2 (S := S) Y)).trans
    ((splitTransport (S := S) Y 2 1).trans (selfTransport (G := PackedFree.pow S Y (2+1)) (BlockEvaluation.global S Y (2+1)) (PackedCuts.sameLength S Y (2,1)).symm))
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
