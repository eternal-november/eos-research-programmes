module
public import ContextualComposition.ContextadTensor
public import Mathlib.CategoryTheory.Yoneda
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadRepresentable
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares SpanPayload.Power
universe b u
variable {B : Type b} [Category.{u} B] {P : Endpoints.{b,u,u,u} B} (S : P.Split)
abbrev rep (D : B) := yoneda.obj D ⋙ typeToCat
theorem unit (d : ContextadUnit.Data P) {A D : B} (f : A ⟶ D) :
    (((ContextadUnit.unit d S).app (rep D)).app (op A)).toFunctor.obj (Discrete.mk f) =
      pair (rep D) _ (d.grade A) (Discrete.mk (d.discharge A ≫ f)) := rfl
theorem tensor (d : ContextadTensor.Data S) {A D : B} (t : Chain P 2 A) (f : endpoint t ⟶ D) :
    (ContextadTensor.binary d (rep D) A).obj (realize (rep D) S t (Discrete.mk f)) =
      pair (rep D) _ ((d.tensor A).obj (gradeObj S 1 A t))
        (Discrete.mk ((d.delta A).app (gradeObj S 1 A t) ≫ f)) :=
  ContextadTensor.binaryObj d (rep D) A t (Discrete.mk f)
theorem gradeTriangle {A D : B} {p q : P.grades.obj (op A)} (a : p ⟶ q)
    (f : (P.extend A).obj p ⟶ D) (g : (P.extend A).obj q ⟶ D) :
    Nonempty ((Discrete.mk f : (rep D).obj (op ((P.extend A).obj p))) ⟶
      ((rep D).map ((P.extend A).map a).op).toFunctor.obj (Discrete.mk g)) ↔ f = (P.extend A).map a ≫ g :=
  ⟨fun ⟨h⟩ => Discrete.eq_of_hom h,fun h => ⟨eqToHom (congrArg Discrete.mk h)⟩⟩
end ContextualComposition.GrothendieckStep.ContextadRepresentable
