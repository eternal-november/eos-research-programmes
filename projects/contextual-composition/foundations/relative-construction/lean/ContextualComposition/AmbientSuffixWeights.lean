module
public import ContextualComposition.AmbientSuffixView
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientSuffixWeights
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
section Two
variable {a b : obj S 0 (obj S 1 X) ⟶ obj S 1 (obj S 1 Y)} (u : a ≅ b) (r : Map S 0 1)
theorem two (h : RRead (X := obj S 1 X) (Y := obj S 1 Y) (i := 0) (j := 1) S (Fx (S := S) f) u r) :
    RRead (X := X) (Y := Y) (i := 1) (j := 2) S f u (suffix r) :=
  AmbientSuffixView.carry f r u.inv (v0 X) (v1 Y) h
end Two
section Three
variable {a b : obj S 2 (obj S 1 X) ⟶ obj S 1 (obj S 1 Y)} (u : a ≅ b) (r : Map S 2 1)
theorem three (h : RRead (X := obj S 1 X) (Y := obj S 1 Y) (i := 2) (j := 1) S (Fx (S := S) f) u r) :
    RRead (X := X) (Y := Y) (i := 3) (j := 2) S f u (suffix r) :=
  AmbientSuffixView.carry f r u.inv (v2 X) (v1 Y) h
end Three
end ContextualComposition.GrothendieckStep.AmbientSuffixWeights
