module
public import ContextualComposition.AmbientTerminalHead
public import ContextualComposition.AmbientChartRows
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFlatTerminal
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadOuterRigidity ContextadDisjointCut AmbientChosenTail
open AmbientBicategory AmbientCoordinates ContextadWeakWeight ContextadWeakAction ContextadCellWhisker AmbientTerminalCones AmbientHorizontalFrames
open ContextadAmbientPayload ContextadModification AmbientNativeTerminal AmbientHorizontalRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
local notation "J₀" => stage (S := S) (underlying X) (power S 1)
theorem reflectStage {a b a' b' : Raw S X 2} (u : a ⟶ b) (v : a' ⟶ b')
    (h : Aligned ((J₀).map u) ((J₀).map v)) : Aligned u v := by
  let V := chart S X 2
  have z := (NativeCube.functorAlign (resolve1 (S := S) X).symm u).trans
    ((h.map (chart S (obj S 1 X) 1)).trans (NativeCube.functorAlign (resolve1 (S := S) X) v))
  exact (NativeCube.functorAlign V.asIsomorphism.unit_eq u).trans ((z.map V.strictInv).trans (NativeCube.functorAlign V.asIsomorphism.unit_eq.symm v))
theorem rowsTwo {a b a' b' : Raw S X 2} (v : a ⟶ b) (c : a' ⟶ b') (l : a = a') (r : b = b')
    (gr : Pure (gradeMap ((J₀).map v))) (gc : Pure (gradeMap ((J₀).map c)))
    (ll : Aligned ((leafAt (underlying (obj S 1 X)) (power S 1).dest).map ((J₀).map v))
      ((chart S X 1).map ((finalOne (S := S) X).map c))) : Aligned v c := by
  let H := J₀
  apply reflectStage X v c
  exact AmbientInsideLetters.alignParts (underlying (obj S 1 X)) (power S 1).dest (congrArg H.obj l) (congrArg H.obj r) _ _ gr gc
    (ll.trans (NativeCube.functorAlign (stageLeaf (S := S) X (power S 1)).symm c))
end
end ContextualComposition.GrothendieckStep.AmbientFlatTerminal
