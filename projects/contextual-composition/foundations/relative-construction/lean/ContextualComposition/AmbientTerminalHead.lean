module
public import ContextualComposition.AmbientTerminalViews
public import ContextualComposition.AmbientChartRows
public import ContextualComposition.AmbientTerminalCones
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNativeTerminal
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open ContextadAmbientPayload ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
abbrev native (x : Raw S X 4) := (rawCell (underlying X) (disjoint f g pg)).hom.app x
theorem stageFront {a b : Raw S X 2} (v : a ⟶ b) (h : Pure (gradeMap (gradeMap v))) :
    Pure (gradeMap ((stage (S := S) X (power S 1)).map v)) :=
  AmbientMateCalculus.pureOfAligned (NativeCube.functorAlign (stageHead (S := S) X (power S 1)) v) h
set_option linter.defProp false in
def stageBase {a b : Raw S X 2} (v : a ⟶ b) (h : Pure (gradeMap ((stage (S := S) X (power S 1)).map v))) :=
  AmbientMateCalculus.pureOfAligned ((NativeCube.functorAlign (stageLeaf (S := S) X (power S 1)).symm v).map (proj (underlying (obj S 1 X))))
    (pureMap (power S 1).dest h)
set_option linter.defProp false in
def originalGrade (x : Raw S X 4) := NativeCube.ofEq (readGrade (disjoint f g pg) (underlying X) x)
set_option linter.defProp false in
def head (x : Raw S X 4) := stageFront X (native X f g pg x)
  (AmbientMateCalculus.pureOfAligned ((originalGrade X f g pg x).map gradeProjection) (assembledHead f g pg _))
set_option linter.defProp false in
def nativeTipGrade (x : Raw S X 4) := ((originalGrade X f g pg x).map (NativeAssoc.last S 1)).trans (NativeCube.ofEq (assembledTip f g pg _))
set_option linter.defProp false in
def nativeBase (x : Raw S X 4) := stageBase X (native X f g pg x)
  (head X f g pg x)
end
end ContextualComposition.GrothendieckStep.AmbientNativeTerminal
