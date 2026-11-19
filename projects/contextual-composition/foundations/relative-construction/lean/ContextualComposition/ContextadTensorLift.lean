module
public import ContextualComposition.ContextadTensor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadTensorLift
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares SpanPayload.Power ContextadUnit
universe b w u v
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} {S : P.Split} (d : ContextadTensor.Data S)
abbrev acc {A : B} (t : Chain P 2 A) := (d.tensor A).obj (gradeObj S 1 A t)
abbrev leg {A : B} (t : Chain P 2 A) := (d.delta A).app (gradeObj S 1 A t)
/-- The two component laws of preserving a chosen cartesian lift.
These mention no presheaf and do not require lift or comparison arrows to be isomorphisms. -/
structure Data : Prop where
  grade : ∀ {A D : B} (a : D ⟶ A) (t : Chain P 2 A),
    (P.grades.map a.op).toFunctor.obj (acc d t) = acc d (pullChain a t)
  square : ∀ {A D : B} (a : D ⟶ A) (t : Chain P 2 A),
    (P.lift a).app (acc d t) ≫ leg d t =
      (P.extend D).map (eqToHom (grade a t)) ≫ leg d (pullChain a t) ≫ endLift a t
variable (h : Data d) (Y : Bᵒᵖ ⥤ Cat.{max u v,u})
abbrev coordinate {A : B} (t : Chain P 2 A) :=
  (Y.map (leg d t).op).toFunctor ⋙ atGrade Y (P.extend A) (acc d t)
include h
theorem coordinateSquare {A D : B} (a : D ⟶ A) (t : Chain P 2 A) :
    (Y.map (endLift a t).op).toFunctor ⋙ coordinate d Y (pullChain a t) =
      coordinate d Y t ⋙ P.baseRestrict Y a := by
  have k := collapsed Y (P.extend D) (h.grade a t) ((P.lift a).app (acc d t) ≫ leg d t)
    (leg d (pullChain a t) ≫ endLift a t) (h.square a t)
  rw [op_comp,Y.map_comp,op_comp,Y.map_comp] at k
  exact k.symm.trans (congrArg ((Y.map (leg d t).op).toFunctor ⋙ ·) (inclRestrict Y _ _ _ (P.lift a) (acc d t)).symm)
theorem objects {A D : B} (a : D ⟶ A) (x : (Iterates.layer P S Y 2).obj (op A)) :
    (ContextadTensor.binary d Y D).obj (((Iterates.layer P S Y 2).map a.op).toFunctor.obj x) =
      (P.baseRestrict Y a).obj ((ContextadTensor.binary d Y A).obj x) := by
  let z := unrealize Y S 2 A x
  have k : realize Y S z.1 z.2 = x := pack_unpack Y S 2 A x
  rw [← k,← realized_pull,ContextadTensor.binaryObj,ContextadTensor.binaryObj]
  exact Functor.congr_obj (coordinateSquare d h Y a z.1) z.2
end ContextualComposition.GrothendieckStep.ContextadTensorLift
