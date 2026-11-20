module
public import ContextualComposition.AmbientAssocPins
public import ContextualComposition.AmbientMultiplicationSpoke
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSuccessorMap
public import ContextualComposition.AmbientOutsideWeightRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocConstraint
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
def one (Z : Obj.{u,v} B) := installed (i := 3) m (firstTwo m) (assocCart m) Z (A m Z) (eA m Z)
set_option linter.defProp false in
def two (Z : Obj.{u,v} B) := installed (i := 3) m (lastTwo m) (presIso C.assoc.grade.symm (assocCart m)) Z (B' m Z) (eB m Z)
theorem localCmp (Z : Obj.{u,v} B) :
    reframe (one m Z) (two m d C Z) (AmbientNativeModification.cmp C.assoc (assocCart m) (presIso C.assoc.grade.symm (assocCart m)) Z) = assoc S Z d m C := rfl
end ContextualComposition.GrothendieckStep.AmbientAssocConstraint
