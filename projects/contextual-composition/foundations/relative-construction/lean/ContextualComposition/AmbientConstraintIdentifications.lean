module
public import ContextualComposition.AmbientConstraintSquares
public import ContextualComposition.AmbientConstraintIsos
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientConstraintIdentifications
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open ContextadNativeLaws ContextadRoutes ContextadLawTransport ContextadModification AmbientSquareBridge
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientUnitSquare AmbientAssocPins AmbientConstraintSquares
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
section Units
variable (r : Map S 1 2) (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
variable (u : ∀ Z : Obj.{u,v} B, obj S 1 Z ⟶ obj S 2 Z) (j : ∀ Z, global (S := S) (i := 1) (j := 2) (underlying Z) r = tot (u Z))
variable (s : K S f ≫ u Y ≅ u X ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
set_option linter.defProp false in
def unit (h : AmbientBoundaryReduction.RRead (i := 1) (j := 2) S f s r) :=
  AmbientConstraintSquares.original (i := 1) (j := 1) (comp r (tensor m)) (cart m r c) (fun Z => u Z ≫ M S Z m) (fun Z => installed m r c Z (u Z) (j Z))
    f rfl (serial s (squareM S m f)) (seam f m r c (j X) (j Y) s h)
end Units
set_option linter.defProp false in
def outerUnit := unit f m (leftUnit d) C.left (fun Z => E S (obj S 1 Z) d) (fun Z => outerE S Z d) (etaK S d f) (AmbientOutsideWeightRead.unit f d)
set_option linter.defProp false in
def innerUnit := unit f m (rightUnit d) C.right (AmbientUnitPins.leg (S := S) d) (AmbientUnitPins.frame (S := S) d) (AmbientUnitPins.letter (S := S) f d) (AmbientUnitWitness.read f d)
set_option linter.defProp false in
def identity := AmbientConstraintSquares.original (i := 1) (j := 1) (ContextadRoutes.identity 1) (fun _ h => h) (fun Z => 𝟙 (obj S 1 Z)) (fun Z => (idRoute S Z 1).symm)
  f rfl (AmbientHorizontalNaturality.identity (K S f)) (AmbientBoundaryReduction.idTarget S f 1)
set_option linter.defProp false in
def first := AmbientConstraintSquares.original (i := 3) (j := 1) (comp (firstTwo m) (tensor m)) (assocCart m) (fun Z => A m Z ≫ M S Z m) (AmbientAssocConstraint.one m)
  f (triple (S := S) f) (serial (AmbientAssocFirstInput.letter f m) (squareM S m f)) (AmbientAssocFirst.bend f m)
set_option linter.defProp false in
def last := AmbientConstraintSquares.original (i := 3) (j := 1) (comp (lastTwo m) (tensor m)) (presIso C.assoc.grade.symm (assocCart m)) (fun Z => B' m Z ≫ M S Z m) (AmbientAssocConstraint.two m d C)
  f (triple (S := S) f) (serial (AmbientAssocLastInput.letter f m) (squareM S m f)) (AmbientAssocLast.bend f m d C)
end ContextualComposition.GrothendieckStep.AmbientConstraintIdentifications
