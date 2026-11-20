module
public import ContextualComposition.AmbientSuffixStage
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixRoutes
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
noncomputable abbrev Fx := AmbientBicategory.map S 1 f
noncomputable abbrev flat := AmbientMateCalculus.q (append P S U).dest (append P S V).dest (appendMap (S := S) r).grade (appendMap (S := S) r).leg f.hom
noncomputable abbrev nested := AmbientMateCalculus.q U.dest V.dest r.grade r.leg (Fx (S := S) f).hom
theorem source :
    lRoute (append P S U).dest (append P S V).dest (appendMap (S := S) r).grade (appendMap (S := S) r).leg f.hom ⋙ stage (S := S) (underlying Y) V =
    stage (S := S) (underlying X) U ⋙ lRoute U.dest V.dest r.grade r.leg (Fx (S := S) f).hom :=
  pairRoutes (AmbientSuffixStage.weight r X) (AmbientSuffixStage.action f V)
theorem target :
    rRoute (append P S U).dest (append P S V).dest (appendMap (S := S) r).grade (appendMap (S := S) r).leg f.hom ⋙ stage (S := S) (underlying Y) V =
    stage (S := S) (underlying X) U ⋙ rRoute U.dest V.dest r.grade r.leg (Fx (S := S) f).hom :=
  pairRoutes (AmbientSuffixStage.action f U) (AmbientSuffixStage.weight r Y)
theorem grade (x) : Pure (gradeMap ((stage (S := S) (underlying Y) V).map ((flat (S := S) f r).app x))) :=
  AmbientMateCalculus.pureOfAligned (NativeCube.functorAlign (stageHead (S := S) (underlying Y) V) _) (pureMap gradeProjection (weakGrade _ _ _ _ f.hom x))
end ContextualComposition.GrothendieckStep.AmbientSuffixRoutes
