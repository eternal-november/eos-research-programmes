module
public import ContextualComposition.AmbientPackedStages
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPackedTips
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open ContextadSchedule ContextadModification ContextadAmbientPayload
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
abbrev wt (x : Raw S X 4) := (wideArrow (underlying X) f).app x
abbrev ft (x : Raw S X 4) := (blocks S 2 2).first.obj (grade (underlying X) (power S 4).dest x)
theorem gradeWt (x : Raw S X 4) : gradeMap (wt X f x) = (move f).app (grade (underlying X) (power S 4).dest x) := rfl
theorem inIndex (x : Raw S X 4) : ft (S := S) X x = grade (underlying (obj S 2 X)) (power S 2).dest ((I (S := S) X).obj x) :=
  Functor.congr_obj (splitFront (S := S) (underlying X) 2 2).symm x
set_option linter.defProp false in
def moveEq (x : Raw S X 4) := (congrArg (power S 2).source.map (gradeWt X f x)).trans (moveBase f (grade (underlying X) (power S 4).dest x))
theorem legAlign (x : Raw S X 4) :
    Aligned ((power S 2).source.map (gradeMap (wt X f x))) (f.leg.app (grade (underlying (obj S 2 X)) _ ((I (S := S) X).obj x))) := by
  rw [moveEq X f x]
  exact ContextadPayloadModification.appChange f.leg (inIndex X x)
set_option linter.defProp false in
def baseIn (x : Raw S X 4) :=
  (NativeCube.functorAlign (BlockEvaluation.globalOver S (underlying X) 2) (wt X f x)).trans (legAlign X f x)
noncomputable def fromRaw (x : Raw S X 4) := (chart S X 2).map (wt X f x)
noncomputable def fromPacked (x : Raw S X 4) := tipAt f (obj S 2 X) ((I (S := S) X).obj x)
def Input (x : Raw S X 4) : Prop := Aligned (C := Total (underlying (obj S 2 X)) (𝟭 B)) (fromRaw X f x) (fromPacked X f x)
end
end ContextualComposition.GrothendieckStep.AmbientPackedTips
