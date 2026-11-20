module
public import ContextualComposition.AmbientUnitWitness
public import ContextualComposition.AmbientUnitConclusion
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientActualUnitFrames
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientUnitInputs
variable (d : ContextadUnit.Data P)
open AmbientUnitSquare AmbientUnitPins
variable (m : ContextadTotal.Native S) (C : Constraints d m)
theorem right (Z : Obj.{u,v} B) :
    constr m (rightUnit d) C.right Z (leg (S := S) d Z) (frame (S := S) d Z) = AmbientHorizontalFrames.right S Z d m C := rfl
theorem left (Z : Obj.{u,v} B) :
    constr m (leftUnit d) C.left Z (E S (obj S 1 Z) d) (outerE S Z d) = AmbientHorizontalFrames.left S Z d m C := rfl
end ContextualComposition.GrothendieckStep.AmbientActualUnitFrames
