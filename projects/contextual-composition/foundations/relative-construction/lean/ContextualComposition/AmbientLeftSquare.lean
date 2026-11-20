module
public import ContextualComposition.AmbientActualUnitFrames
public import ContextualComposition.AmbientOutsideWeightRead
public import ContextualComposition.AmbientRightWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLeftSquare
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
variable (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def close := AmbientUnitConclusion.conclude (a := E S (obj S 1 X) d) (b := E S (obj S 1 Y) d)
  f m (leftUnit d) C.left (outerE S X d) (outerE S Y d) (etaK S d f) (etaK S d f) (left S X d m C) (left S Y d m C)
  rfl (AmbientActualUnitFrames.left d m C X) (AmbientActualUnitFrames.left d m C Y) (AmbientOutsideWeightRead.unit f d)
theorem original : Left S d m C f := close f d m C
end ContextualComposition.GrothendieckStep.AmbientLeftSquare
