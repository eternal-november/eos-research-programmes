module
public import ContextualComposition.AmbientUnitInputs
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitPins
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
noncomputable def leg (Z : Obj.{u,v} B) : obj S 1 Z ⟶ obj S 2 Z := K S (E S Z d)
theorem frame (Z : Obj.{u,v} B) : global Z (rightUnit d) = tot (leg (S := S) d Z) := innerE S Z d
noncomputable def letter : K S f ≫ leg (S := S) d Y ≅ leg (S := S) d X ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f) := kEta S d f
end ContextualComposition.GrothendieckStep.AmbientUnitPins
