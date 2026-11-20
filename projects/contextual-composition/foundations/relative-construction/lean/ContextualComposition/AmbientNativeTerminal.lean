module
public import ContextualComposition.AmbientPackedOutput
public import ContextualComposition.AmbientInputIndex
public import ContextualComposition.AmbientChartRows
public import ContextualComposition.AmbientTerminalHead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNativeTerminal
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open ContextadAmbientPayload ContextadModification AmbientPackedTips
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
abbrev ambient (x : Raw S X 4) := (AmbientComparisonRead.q S f (oper S g pg X)).app ((I (S := S) X).obj x)
set_option linter.defProp false in
def rightPacked (x : Raw S X 4) := (outputTip X f g pg x).symm.trans ((rightRead (underlying X) f g x).symm.map (chart S X 1))
set_option linter.defProp false in
def leftPacked (x : Raw S X 4) (hi : Input X f x) :=
  (hi.symm.map (tot (oper S g pg X))).trans (operTail X g pg (wt X f x))
set_option linter.defProp false in
def actualFactor (x : Raw S X 4) := AmbientMateCalculus.factor _ _ f.grade f.leg (oper S g pg X).hom ((I (S := S) X).obj x)
set_option linter.defProp false in
def sqLeft (x : Raw S X 4) (hi : Input X f x) := (actualFactor X f g pg x).trans (leftPacked X f g pg x hi)
set_option linter.defProp false in
def sqRight (x : Raw S X 4) :=
  let V := chart S X 1
  let c := (finalOne (S := S) (underlying X)).map (native X f g pg x)
  let j := AmbientTerminalCones.right (underlying X) f g x
  ((rawFactor (underlying X) f g pg x).symm.map V).trans (NativeCube.ofEq (V.map_comp c j))
set_option linter.defProp false in
def sqBoth (x : Raw S X 4) (hi : Input X f x) := (sqLeft X f g pg x hi).trans (sqRight X f g pg x)
set_option linter.defProp false in
def weakBase (x : Raw S X 4) := pureMap (power S 1).dest (weakGrade _ _ f.grade f.leg (oper S g pg X).hom ((I (S := S) X).obj x))
theorem finish {D L : Type*} [Category* D] [Category* L] (π : D ⥤ L)
    {a b c a' b' c' : D} {h : a ⟶ b} {j : b ⟶ c} {h' : a' ⟶ b'} {j' : b' ⟶ c'}
    (sq : Aligned (h ≫ j) (h' ≫ j')) (rc : Aligned j j')
    (ct : NativeCleavage.Cartesian π j) (p : Pure (π.map h)) (q : Pure (π.map h')) :
    Aligned h h' := AmbientChartRows.alignCancel π ct (alignTransports (congrArg π.obj sq.src) p q) rc sq
set_option linter.defProp false in
def tailFrom (x : Raw S X 4) (hi : Input X f x) :=
  let π := proj (underlying (obj S 1 X))
  let sq := sqBoth X f g pg x hi
  let rc := rightPacked X f g pg x
  finish π sq rc (tipCart _ _ _ f.grade f.leg _) (weakBase X f g pg x) (nativeBase X f g pg x)
end
end ContextualComposition.GrothendieckStep.AmbientNativeTerminal
