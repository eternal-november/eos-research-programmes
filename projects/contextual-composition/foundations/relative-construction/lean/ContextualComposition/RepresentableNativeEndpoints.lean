module
public import ContextualComposition.RepresentableKleisliData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableNativeEndpoints
open CategoryTheory CategoryTheory.Functor Opposite
open RepresentableKleisli RepresentableComma
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B}
variable {A D A' D' : B}
abbrev Arg (A D : B) := Row (P.extend A) D
def post (v : D ⟶ D') (x : Arg (P := P) A D) : Arg (P := P) A D' :=
  pair (RepresentableYoneda.rep D') (P.extend A) (grade _ _ x) (Discrete.mk (body _ _ x ≫ v))
def pre (u : A ⟶ A') (y : Arg (P := P) A' D') : Arg (P := P) A D' :=
  (P.baseRestrict (RepresentableYoneda.rep D') u).obj y
theorem preFormula (u : A ⟶ A') (y : Arg (P := P) A' D') :
    pre u y = pair (RepresentableYoneda.rep D') (P.extend A) ((P.grades.map u.op).toFunctor.obj (grade _ _ y))
      (Discrete.mk ((P.lift u).app (grade _ _ y) ≫ body _ _ y)) := rfl
def Square (u : A ⟶ A') (v : D ⟶ D') (x : Arg (P := P) A D) (y : Arg (P := P) A' D') :=
  { h : grade _ _ x ⟶ (P.grades.map u.op).toFunctor.obj (grade _ _ y) //
    body _ _ x ≫ v = (P.extend A).map h ≫ (P.lift u).app (grade _ _ y) ≫ body _ _ y }
def edgeEquiv (u : A ⟶ A') (v : D ⟶ D') (x : Arg (P := P) A D) (y : Arg (P := P) A' D') :
    (post v x ⟶ pre u y) ≃ Square u v x y where
  toFun h := ⟨gradeMap h, (triangle (P.extend A) D' h).symm⟩
  invFun h := arrow h.val (eqToHom (congrArg Discrete.mk h.property))
  left_inv h := arrowExt _ _ _ _ rfl
  right_inv h := Subtype.ext (by rfl)
theorem gradeRetained (u : A ⟶ A') (v : D ⟶ D') (x : Arg (P := P) A D) (y : Arg (P := P) A' D') (h : post v x ⟶ pre u y) :
    (edgeEquiv u v x y h).val = gradeMap h := rfl
end ContextualComposition.GrothendieckStep.RepresentableNativeEndpoints
