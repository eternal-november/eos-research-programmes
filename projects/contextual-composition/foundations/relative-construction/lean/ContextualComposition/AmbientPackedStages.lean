module
public import ContextualComposition.AmbientTerminalViews
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPackedTips
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open ContextadSchedule ContextadModification ContextadAmbientPayload
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong NativeBlocks.blocks ContextadRoutes.inside
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
abbrev I := splitAt (S := S) (underlying X) 2 2
abbrev J := stage (S := S) (underlying X) (power S 1)
set_option linter.defProp false in
def inputLeaf :=
  (splitTail (S := S) X 2 2).trans (congrArg (· ⋙ chart S X 2) (tail2Frame (S := S) X))
abbrev E (n : Nat) := (power S n).dest
abbrev tipAt (Y : Obj.{u,v} B) (x : Raw S Y 2) := (tip (underlying Y) (E (S := S) 2) (E (S := S) 1) f.grade f.leg).app x
set_option linter.defProp false in
def outputLeaf :=
  (splitTail (S := S) X 2 1).trans (congrArg (· ⋙ chart S X 1) (tail1Frame (S := S) X))
theorem operTail {a b : Raw S X 2} (v : a ⟶ b) :
    Aligned ((tot (oper S g pg X)).map ((chart S X 2).map v)) ((chart S X 1).map ((raw X g).map v)) :=
  (NativeCube.functorAlign (congrArg (chart S X 2 ⋙ ·) (totalOper S X g pg)) v).trans (NativeCube.functorAlign (ContextadRecognition.eraseInv (chart S X 2) _) v)
end
end ContextualComposition.GrothendieckStep.AmbientPackedTips
