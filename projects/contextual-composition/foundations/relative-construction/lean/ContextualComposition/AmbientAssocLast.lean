module
public import ContextualComposition.AmbientGuardSpoke
public import ContextualComposition.AmbientAssocLastInput
public import ContextualComposition.AmbientAssocConstraint
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocLast
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
def bend := AmbientGuardSpoke.seam (i := 3) (a := B' m X) (b := B' m Y) f m (triple (S := S) f) (lastTwo m) (presIso C.assoc.grade.symm (assocCart m)) (eB m X) (eB m Y) (AmbientAssocLastInput.letter f m) (AmbientAssocLastInput.read f m)
end ContextualComposition.GrothendieckStep.AmbientAssocLast
