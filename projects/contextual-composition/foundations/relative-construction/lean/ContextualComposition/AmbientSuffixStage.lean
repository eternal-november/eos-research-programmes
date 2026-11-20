module
public import ContextualComposition.AmbientSuffixFactor
public import ContextualComposition.AmbientInsideMate
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixStage
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadInsideCells ContextadLawTransport
open ContextadOuterCharts SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames AmbientMateReindex ContextadWeakWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
open ContextadOuterRigidity ContextadChosenCone BoundaryPaste
variable (f : X ⟶ Y) (U : Span (B := B))
variable (b : obj S 1 X ⟶ obj S 1 Y)
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong stage
theorem framed (v : atEndpoint f.hom (right P S) ⋙ chart S Y 1 = chart S X 1 ⋙ totalStrong b.hom) :
    atEndpoint f.hom (append P S U).dest ⋙ stage (S := S) (underlying Y) U =
      stage (S := S) (underlying X) U ⋙ atEndpoint b.hom U.dest := by
  let H := atEndpoint f.hom (append P S U).dest
  let T := totalStrong b.hom
  let V := stage (S := S) (underlying X) U
  apply fold_ext
  · apply (congrArg (H ⋙ ·) (stageHead (S := S) (underlying Y) U)).trans
    apply (congrArg (· ⋙ gradeProjection) (actionGrade _ (totalStrong f.hom) (strongOver f.hom))).trans
    exact ((congrArg (V ⋙ ·) (actionGrade U.dest T (strongOver b.hom))).trans (stageHead (S := S) (underlying X) U)).symm
  · apply (congrArg (H ⋙ ·) (stageLeaf (S := S) (underlying Y) U)).trans
    apply (congrArg (· ⋙ chart S Y 1) (actionPull f.hom (right P S) (second P U.dest) rfl).symm).trans
    apply (congrArg (ContextadOuterCharts.last (S := S) (underlying X) U ⋙ ·) v).trans
    have a := congrArg (fun z : Total (underlying X) (append P S U).dest ⥤ Total (underlying (obj S 1 X)) (𝟭 B) => z ⋙ T) (stageLeaf (S := S) (underlying X) U).symm
    have b := congrArg (V ⋙ ·) (actionLeaf U.dest T (strongOver b.hom)).symm
    simp only [Functor.assoc] at a b ⊢
    exact a.trans b
theorem action :
    atEndpoint f.hom (append P S U).dest ⋙ stage (S := S) (underlying Y) U =
      stage (S := S) (underlying X) U ⋙ atEndpoint (AmbientBicategory.map S 1 f).hom U.dest :=
  framed f U (AmbientBicategory.map S 1 f) (AmbientInsideMate.chartAction f 1)
variable {U} {V : Span (B := B)} (r : Operation U V)
theorem weight (Z : Obj.{u,v} B) : fstWay (S := S) (underlying Z) r = sndWay (S := S) (underlying Z) r :=
  functorRigid (stageComparison (S := S) (underlying Z) r) (stagePure (S := S) (underlying Z) r)
theorem chosen (Z : Obj.{u,v} B) (x) :
    Aligned ((chart S Z 1).map ((gLift (S := S) (underlying Z) r).app x))
      ((tip (LY (S := S) (underlying Z)) U.dest V.dest r.grade r.leg).app ((stage (S := S) (underlying Z) U).obj x)) := by
  let W := underlying Z
  have h := joinAligned (wr (S := S) W r) (stage (S := S) W V) (NativeTrace.leaf (LY (S := S) W) V.dest)
    (ContextadOuterCharts.last (S := S) W V) (BlockEvaluation.global S W 1) (ContextadOuterCharts.last (S := S) W U) (prior (S := S) W U)
    (stageLeaf (S := S) W V) (stageLeaf (S := S) W U).symm (leftCore (S := S) W r) x
  exact h.symm.trans (bothChosen W r x)
end ContextualComposition.GrothendieckStep.AmbientSuffixStage
