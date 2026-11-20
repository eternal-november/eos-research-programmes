module
public import ContextualComposition.AmbientSquareGuard
public import ContextualComposition.AmbientSuffixWeights
public import ContextualComposition.AmbientSuffixView
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixGuard
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadLawTransport ContextadOuterCharts
open SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames ContextadWeakWeight AmbientInsideMateRead
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
open AmbientSuffixRoutes AmbientBoundaryReduction
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell stage
open AmbientSuffixView
variable (f : X ⟶ Y)
open AmbientSquareGuard
variable {a b : obj S 2 (obj S 1 X) ⟶ obj S 1 (obj S 1 Y)} (u : a ≅ b) (r : Map S 2 1)
theorem three (h : RRead (X := obj S 1 X) (Y := obj S 1 Y) (i := 2) (j := 1) S (Fx (S := S) f) u r) :
    Guard (X := X) (Y := Y) (i := 3) (j := 2) f (suffix r) u :=
  pack (i := 3) (j := 2) f (suffix r) u (AmbientSuffixWeights.three f u r h)
end ContextualComposition.GrothendieckStep.AmbientSuffixGuard
