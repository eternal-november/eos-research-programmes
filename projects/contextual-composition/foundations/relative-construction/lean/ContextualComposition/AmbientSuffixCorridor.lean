module
public import ContextualComposition.AmbientSuffixRoutes
public import ContextualComposition.AmbientChartRows
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixCorridor
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts
open SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames ContextadWeakWeight AmbientInsideMateRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
variable (f : X ⟶ Y) {U V : Span (B := B)} (r : Operation U V)
open AmbientSuffixRoutes
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong stage
theorem packed (x : Total (underlying X) (append P S U).dest) :
    Aligned ((chart S Y 1).map ((ContextadOuterCharts.last (S := S) (underlying Y) V).map ((flat (S := S) f r).app x)) ≫
      (chart S Y 1).map ((gLift (S := S) (underlying Y) r).app ((atEndpoint f.hom (append P S U).dest).obj x)))
      ((totalStrong (Fx (S := S) f).hom).map ((tip (LY (S := S) (underlying X)) U.dest V.dest r.grade r.leg).app ((stage (S := S) (underlying X) U).obj x))) := by
  apply (NativeCube.ofEq ((chart S Y 1).map_comp _ _).symm).trans
  apply ((AmbientSuffixFactor.natural f.hom (right P S) (second P U.dest) (second P V.dest) (r₀ (P := P) r) (α (P := P) r) x).map (chart S Y 1)).trans
  apply (NativeCube.functorAlign (AmbientInsideMate.chartAction f 1) ((gLift (S := S) (underlying X) r).app x)).trans
  exact (AmbientSuffixStage.chosen r X x).map (totalStrong (Fx (S := S) f).hom)
theorem terminal (x : Total (underlying X) (append P S U).dest) :
    Aligned ((leafAt (LY (S := S) (underlying Y)) V.dest).map ((stage (S := S) (underlying Y) V).map ((flat (S := S) f r).app x)))
      ((leafAt (LY (S := S) (underlying Y)) V.dest).map ((nested (S := S) f r).app ((stage (S := S) (underlying X) U).obj x))) := by
  let z := (atEndpoint f.hom (append P S U).dest).obj x
  let N := tip (LY (S := S) (underlying Y)) U.dest V.dest r.grade r.leg
  let y := (stage (S := S) (underlying X) U).obj x
  let π := proj (LY (S := S) (underlying Y))
  have endTip := (AmbientSuffixStage.chosen r Y z).trans (ContextadPayloadModification.appChange N (Functor.congr_obj (AmbientSuffixStage.action f U) x))
  have sq := (packed f r x).trans (AmbientMateCalculus.factor U.dest V.dest r.grade r.leg (Fx (S := S) f).hom y).symm
  have obs := NativeCube.functorAlign (stageLeaf (S := S) (underlying Y) V) ((flat (S := S) f r).app x)
  apply obs.trans; apply Aligned.symm
  apply AmbientChartRows.alignCancel π (tipCart _ U.dest V.dest r.grade r.leg _) _ endTip.symm sq.symm
  apply ContextadOuterRigidity.alignTransports (congrArg π.obj sq.src.symm)
  · exact pureMap V.dest (weakGrade U.dest V.dest r.grade r.leg (Fx (S := S) f).hom y)
  · exact AmbientMateCalculus.pureOfAligned (obs.symm.map π) (pureMap V.dest (AmbientSuffixRoutes.grade f r x))
end ContextualComposition.GrothendieckStep.AmbientSuffixCorridor
