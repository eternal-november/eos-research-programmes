module
public import ContextualComposition.AmbientActualUnitFrames
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientRightSquare
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
variable (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def close := AmbientUnitConclusion.conclude (a := leg (S := S) d X) (b := leg (S := S) d Y) f m (rightUnit d) C.right
  (frame (S := S) d X) (frame (S := S) d Y) (letter (S := S) f d) (kEta S d f) (right S X d m C) (right S Y d m C)
  rfl (AmbientActualUnitFrames.right d m C X) (AmbientActualUnitFrames.right d m C Y) (AmbientUnitWitness.read f d)
theorem original : Right S d m C f := close f d m C
end ContextualComposition.GrothendieckStep.AmbientRightSquare
