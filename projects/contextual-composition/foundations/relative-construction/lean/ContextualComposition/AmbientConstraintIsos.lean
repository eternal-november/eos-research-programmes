module
public import ContextualComposition.AmbientTypedConstraint
public import ContextualComposition.AmbientRebasedStrong
public import ContextualComposition.AmbientCoherentObserver
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientConstraintIsos
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open ContextadNativeLaws ContextadRoutes ContextadLawTransport ContextadModification AmbientSquareBridge
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
universe u v
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientTypedConstraint ContextadOuterCharts
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
section Units
variable (r : Map S 1 2) (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
variable (u : ∀ Z : Obj.{u,v} B, obj S 1 Z ⟶ obj S 2 Z) (j : ∀ Z, global (S := S) (i := 1) (j := 2) (underlying Z) r = tot (u Z))
noncomputable def unit := AmbientTypedConstraint.iso (comp r (tensor m)) (ContextadRoutes.identity 1) (AmbientUnitSquare.cart m r c) (fun _ h => h) c
  (fun Z => u Z ≫ M S Z m) (fun Z => 𝟙 (obj S 1 Z)) (fun Z => AmbientUnitSquare.installed m r c Z (u Z) (j Z)) (fun Z => (idRoute S Z 1).symm)
variable (Z : Obj.{u,v} B) (k : u Z ≫ M S Z m ≅ 𝟙 (obj S 1 Z))
theorem unitApp (h : AmbientUnitSquare.constr m r c Z (u Z) (j Z) = k) : (unit m r c u j).hom.as.app Z = k.hom := congrArg Iso.hom h
end Units
noncomputable def left := unit m (leftUnit d) C.left (fun Z => E S (obj S 1 Z) d) (fun Z => outerE S Z d)
noncomputable def right := unit m (rightUnit d) C.right (AmbientUnitPins.leg (S := S) d) (AmbientUnitPins.frame (S := S) d)
open AmbientAssocPins
noncomputable def assoc := AmbientTypedConstraint.iso (i := 3) (j := 1) (comp (firstTwo m) (tensor m)) (comp (lastTwo m) (tensor m)) (assocCart m) (presIso C.assoc.grade.symm (assocCart m)) C.assoc
  (fun Z => A m Z ≫ M S Z m) (fun Z => B' m Z ≫ M S Z m) (AmbientAssocConstraint.one m) (AmbientAssocConstraint.two m d C)
variable (Z : Obj.{u,v} B)
theorem leftApp : (left d m C).hom.as.app Z = (AmbientHorizontalFrames.left S Z d m C).hom :=
  unitApp m (leftUnit d) C.left (fun Z => E S (obj S 1 Z) d) (fun Z => outerE S Z d) Z _ (AmbientActualUnitFrames.left d m C Z)
theorem rightApp : (right d m C).hom.as.app Z = (AmbientHorizontalFrames.right S Z d m C).hom :=
  unitApp m (rightUnit d) C.right (AmbientUnitPins.leg (S := S) d) (AmbientUnitPins.frame (S := S) d) Z _ (AmbientActualUnitFrames.right d m C Z)
theorem assocApp : (assoc d m C).hom.as.app Z = (AmbientHorizontalFrames.assoc S Z d m C).hom :=
  congrArg Iso.hom (AmbientAssocConstraint.localCmp m d C Z)
end ContextualComposition.GrothendieckStep.AmbientConstraintIsos
