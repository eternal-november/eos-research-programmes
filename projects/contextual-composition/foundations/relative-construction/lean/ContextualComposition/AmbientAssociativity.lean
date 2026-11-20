module
public import ContextualComposition.AmbientShapeBridge
public import ContextualComposition.AmbientAssocFirst
public import ContextualComposition.AmbientAssocLast
public import ContextualComposition.AmbientGuardSpoke
public import ContextualComposition.AmbientAssocFirstInput
public import ContextualComposition.AmbientAssocConstraint
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssociativity
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
def close := AmbientNamedSquare.close (i := 3) (j := 1) (p := comp (firstTwo m) (tensor m)) (q := comp (lastTwo m) (tensor m))
  (a := front (S := S) f) (u := A m X ≫ M S X m) (u' := A m Y ≫ M S Y m) (v := B' m X ≫ M S X m) (v' := B' m Y ≫ M S Y m)
  f C.assoc (assocCart m) (presIso C.assoc.grade.symm (assocCart m)) (triple (S := S) f)
  (AmbientAssocConstraint.one m X) (AmbientAssocConstraint.one m Y) (AmbientAssocConstraint.two m d C X) (AmbientAssocConstraint.two m d C Y)
  (serial (AmbientAssocFirstInput.letter f m) (squareM S m f)) (serial (AmbientAssocLastInput.letter f m) (squareM S m f))
  (AmbientAssocFirst.bend f m) (AmbientAssocLast.bend f m d C)
  (assoc S X d m C) (assoc S Y d m C) (AmbientAssocConstraint.localCmp m d C X) (AmbientAssocConstraint.localCmp m d C Y)
set_option linter.defProp false in
def actual := AmbientShapeBridge.changeEdges (serial (AmbientAssocFirstInput.letter f m) (squareM S m f)) (serial (AmbientAssocLastInput.letter f m) (squareM S m f)) (assoc S X d m C) (assoc S Y d m C)
  (serial (muK S m f) (squareM S m f)) (serial (kMu S m f) (squareM S m f)) rfl rfl (close f m d C)
set_option linter.defProp false in
def square := AmbientShapeBridge.toSquare (serial (muK S m f) (squareM S m f)) (serial (kMu S m f) (squareM S m f)) (assoc S X d m C) (assoc S Y d m C) (actual f m d C)
theorem original : Assoc S d m C f := square f m d C
end ContextualComposition.GrothendieckStep.AmbientAssociativity
