module
public import ContextualComposition.AmbientNestedGrade
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientChosenTail
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut
open AmbientBicategory AmbientCoordinates ContextadWeakWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
attribute [local irreducible] BlockEvaluation.global
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev finalOne := ContextadOuterCharts.last (S := S) Y (power S 1)
theorem packedTwo {a b : Total Y (power S 2).dest} (v : a ⟶ b)
    (h : Pure (payloadMap (gradeMap (gradeMap v))))
    (j : Pure (payloadMap (gradeMap ((finalOne (S := S) Y).map v))))
    (k : Pure (payloadMap ((finalOne (S := S) Y).map v))) :
    Pure (payloadMap ((BlockEvaluation.global S Y 2).map v)) := by
  apply payloadAligned (Y := PackedFree.pow S Y 2) (e := 𝟭 B) (NativeCube.functorAlign (resolve1 (S := S) Y).symm v)
  apply decodedChosen (S := S) (LY (S := S) Y) ((stage (S := S) Y (power S 1)).map v)
  · exact payloadAligned (Y := P.grades) (e := 𝟭 B) (NativeCube.functorAlign (stageHead (S := S) Y (power S 1)) v) h
  · exact payloadAligned (Y := LY (S := S) Y) (e := 𝟭 B) (NativeCube.functorAlign (stageLeaf (S := S) Y (power S 1)) v)
      (decodedChosen (S := S) Y _ j k)
variable (f : Map S 2 1)
abbrev tailTwo (U : Span (B := B)) := SpanPayload.totalMap Y (leaf S U) (power S 2).dest rfl
abbrev wideArrow := liftTail Y (power S 2).dest (wide f).grade (move f)
theorem packedWide (x : Total Y (power S 4).dest) :
    Pure (payloadMap ((BlockEvaluation.global S Y 2).map ((wideArrow Y f).app x))) :=
  packedTwo Y _ (pureId _) (pureId _) (pureId _)
theorem packedSnoc (x : Total Y (power S 3).dest) :
    Pure (payloadMap ((BlockEvaluation.global S Y 1).map ((gLift (S := S) (U := power S 2) (V := power S 1) Y f).app x))) :=
  decodedChosen Y _ (pureId _) (pureId _)
end
end ContextualComposition.GrothendieckStep.AmbientChosenTail
