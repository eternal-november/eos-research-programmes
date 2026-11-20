module
public import ContextualComposition.AmbientInsideGuard
public import ContextualComposition.AmbientAssocConstraint
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocLastInput
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1550000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
open AmbientAssocPins AmbientMultiplicationSpoke
variable (d : ContextadUnit.Data P) (C : Constraints d m)
noncomputable def letter : front (S := S) f ≫ B' m Y ≅ B' m X ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f) := kMu S m f
theorem read : AmbientSquareGuard.Guard (i := 3) (j := 2) f (lastTwo m) (letter f m) := AmbientInsideGuard.actual f m
end ContextualComposition.GrothendieckStep.AmbientAssocLastInput
