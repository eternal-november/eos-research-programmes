module
public import ContextualComposition.AmbientSuffixMateRead
public import ContextualComposition.ContextadAppendCells
public import ContextualComposition.AmbientInsideMate
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixCells
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
open ContextadAppendCells
variable {U V : Span (B := B)} {r s : Operation U V}
variable (c : ApexCell r s) (Z : Obj.{u,v} B)
noncomputable abbrev weight (G : Bᵒᵖ ⥤ Cat.{max u v,u}) :=
  WeightedCells.weightIso G U.dest V.dest c.grade c.tip
noncomputable abbrev outer := weight (appendCell (S := S) c) (underlying Z)
noncomputable abbrev inner := weight c (LY (S := S) (underlying Z))
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong stage
theorem prefixGrade (x : Total (underlying Z) (append P S U).dest) :
    Aligned (gradeMap ((stage (S := S) (underlying Z) V).map ((outer (S := S) c Z).hom.app x)))
      (gradeMap ((inner (S := S) c Z).hom.app ((stage (S := S) (underlying Z) U).obj x))) := by
  let G := underlying Z
  let A := appendCell (S := S) c
  apply (NativeCube.functorAlign (stageHead (S := S) G V) ((outer (S := S) c Z).hom.app x)).trans
  apply ((NativeCube.ofEq (WeightedCells.weightGrade G _ _ A.grade A.tip x)).map gradeProjection).trans
  apply (NativeCube.ofEq (WeightedCells.weightGrade P.grades _ _ c.grade c.tip (grade G _ x))).trans
  apply (ContextadPayloadModification.appChange c.grade.hom (Functor.congr_obj (stageHead (S := S) G U).symm x)).trans
  exact (NativeCube.ofEq (WeightedCells.weightGrade (LY (S := S) G) _ _ c.grade c.tip _)).symm
theorem terminal (x : Total (underlying Z) (append P S U).dest) :
    Pure (payloadMap ((stage (S := S) (underlying Z) V).map ((outer (S := S) c Z).hom.app x))) := by
  let G := underlying Z
  let A := appendCell (S := S) c
  let a := (outer (S := S) c Z).hom.app x
  let π := ContextadOuterCharts.last (S := S) G V
  have t := NativeCube.functorAlign (stageLeaf (S := S) G V) a
  apply ContextadOuterRigidity.payloadAligned (Y := LY (S := S) G) (e := 𝟭 B) t
  apply ContextadOuterRigidity.decodedChosen (S := S) G (π.map a)
  · change Pure (payloadMap (gradeMap a))
    rw [show gradeMap a = _ from WeightedCells.weightGrade G _ _ A.grade A.tip x]
    exact WeightedCells.weightPayloadPure P.grades _ _ c.grade c.tip _
  · exact WeightedCells.weightPayloadPure G _ _ A.grade A.tip x
theorem staged (x : Total (underlying Z) (append P S U).dest) :
    Aligned ((stage (S := S) (underlying Z) V).map ((outer (S := S) c Z).hom.app x))
      ((inner (S := S) c Z).hom.app ((stage (S := S) (underlying Z) U).obj x)) :=
  alignChosen (LY (S := S) (underlying Z)) V.dest (Functor.congr_obj (AmbientSuffixStage.weight s Z) x)
    (prefixGrade c Z x) (terminal c Z x) (WeightedCells.weightPayloadPure _ _ _ c.grade c.tip _)
end ContextualComposition.GrothendieckStep.AmbientSuffixCells
