module
public import ContextualComposition.ContextadOuterBase
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage BoundaryPaste
open ContextadRoutes ContextadWeakAction TelescopeSquares
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,max u v} B)
abbrev LY := PackedFree.pow S Y 1
abbrev head (U : Span (B := B)) := gradeProjection (Y := Y) (e := (append P S U).dest) ⋙ gradeProjection
abbrev last (U : Span (B := B)) := SpanPayload.totalMap Y (second P U.dest) (right P S) rfl
noncomputable def stage (U : Span (B := B)) :=
  attachLast (P := projectionData (LY (S := S) Y)) U.dest (head (S := S) Y U) (last (S := S) Y U ⋙ BlockEvaluation.global S Y 1)
    ((congrArg (last (S := S) Y U ⋙ ·) (BlockEvaluation.globalOver S Y 1)).symm)
theorem stageHead (U : Span (B := B)) : stage (S := S) Y U ⋙ gradeProjection = head (S := S) Y U := attach_prefix .. 
theorem stageLeaf (U : Span (B := B)) : stage (S := S) Y U ⋙ NativeTrace.leaf (LY (S := S) Y) U.dest =
    last (S := S) Y U ⋙ BlockEvaluation.global S Y 1 := attach_last ..
variable {U V : Span (B := B)} (r : Operation U V)
abbrev r₀ := restrict P.grades U.dest V.dest r.grade r.leg
abbrev α := suffixRaw (P := P) (U := U) (V := V) r.grade r.leg
abbrev wr := restrict Y (append P S U).dest (append P S V).dest (appendMap (S := S) r).grade (appendMap (S := S) r).leg
noncomputable abbrev fstWay := wr (S := S) Y r ⋙ stage (S := S) Y V
noncomputable abbrev sndWay := stage (S := S) Y U ⋙ restrict (LY (S := S) Y) U.dest V.dest r.grade r.leg
noncomputable abbrev prior (U : Span (B := B)) := stage (S := S) Y U ⋙ NativeTrace.leaf (LY (S := S) Y) U.dest
theorem gradeEq : fstWay (S := S) Y r ⋙ gradeProjection = sndWay (S := S) Y r ⋙ gradeProjection :=
  (congrArg (wr (S := S) Y r ⋙ ·) (stageHead (S := S) Y V)).trans
    (congrArg (· ⋙ r.grade) (stageHead (S := S) Y U)).symm
abbrev gLift := liftTail Y (right P S) (r₀ (P := P) r) (α (P := P) r)
end ContextualComposition.GrothendieckStep.ContextadOuterCharts
