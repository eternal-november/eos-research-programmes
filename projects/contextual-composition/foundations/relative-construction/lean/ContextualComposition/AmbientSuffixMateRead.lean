module
public import ContextualComposition.AmbientSuffixCorridor
public import ContextualComposition.AmbientChartRows
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixMateRead
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
theorem read (x : Total (underlying X) (append P S U).dest) :
    Aligned ((stage (S := S) (underlying Y) V).map ((flat (S := S) f r).app x))
      ((nested (S := S) f r).app ((stage (S := S) (underlying X) U).obj x)) :=
  AmbientInsideLetters.alignParts _ V.dest (Functor.congr_obj (source f r) x) (Functor.congr_obj (target f r) x)
    _ _ (AmbientSuffixRoutes.grade f r x) (weakGrade U.dest V.dest r.grade r.leg (Fx (S := S) f).hom _) (AmbientSuffixCorridor.terminal f r x)
end ContextualComposition.GrothendieckStep.AmbientSuffixMateRead
