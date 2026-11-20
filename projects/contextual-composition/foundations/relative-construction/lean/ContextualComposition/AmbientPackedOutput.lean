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
set_option maxHeartbeats 2000000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong NativeBlocks.blocks ContextadRoutes.inside
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (pg : gradeCart g)
theorem outputTip (x : Raw S X 4) :
    Aligned ((chart S X 1).map (rTail (underlying X) f g x))
      (tipAt f (obj S 1 X) ((atEndpoint (oper S g pg X).hom (E (S := S) 2)).obj ((I (S := S) X).obj x))) := by
  let z := (inner (underlying X) g).obj x
  have e := AmbientInsideLetters.framePoint X 2 (oper S g pg X) g (totalOper S X g pg) x
  apply ContextadChosenCone.alignChosen (underlying (obj S 1 X)) (𝟭 B)
    ((Functor.congr_obj (outputLeaf (S := S) X).symm z).trans (congrArg (leafAt (underlying (obj S 1 X)) (E (S := S) 2)).obj e))
  · apply (NativeCube.functorAlign (BlockEvaluation.globalOver S (underlying X) 1) _).trans
    apply (snocBase f _).trans
    exact ContextadPayloadModification.appChange f.leg ((Functor.congr_obj (frontOne (S := S) 2).symm (grade (underlying X) (power S 3).dest z)).trans ((Functor.congr_obj (splitFront (S := S) (underlying X) 2 1).symm z).trans (congrArg (grade (underlying (obj S 1 X)) _) e)))
  · exact packedSnoc X f z
  · exact pureId _
end
end ContextualComposition.GrothendieckStep.AmbientPackedTips
