module
public import ContextualComposition.AmbientGuardSpoke
public import ContextualComposition.AmbientAssocFirstInput
public import ContextualComposition.AmbientAssocConstraint
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocFirst
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
set_option linter.defProp false in
def bend := AmbientGuardSpoke.seam (i := 3) (a := A m X) (b := A m Y) f m (triple (S := S) f) (firstTwo m) (assocCart m) (eA m X) (eA m Y) (AmbientAssocFirstInput.letter f m) (AmbientAssocFirstInput.read f m)
end ContextualComposition.GrothendieckStep.AmbientAssocFirst
