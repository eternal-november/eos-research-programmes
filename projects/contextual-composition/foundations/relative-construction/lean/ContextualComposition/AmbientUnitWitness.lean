module
public import ContextualComposition.AmbientUnitPins
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitWitness
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
open AmbientUnitPins
theorem read : RRead (i := 1) (j := 2) S f (letter (S := S) f d) (rightUnit d) := AmbientRightWeight.read f d
noncomputable def data : Boundary (S := S) f (rightUnit d) :=
  ⟨leg (S := S) d X,leg (S := S) d Y,frame (S := S) d X,frame (S := S) d Y,letter (S := S) f d,read (S := S) f d⟩
end ContextualComposition.GrothendieckStep.AmbientUnitWitness
