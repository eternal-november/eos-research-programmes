module
public import ContextualComposition.ContentCovariantGrothendieck
public import ContextualComposition.RepresentableYoneda
public import Mathlib.CategoryTheory.Yoneda
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCorepresentableChart
open CategoryTheory CategoryTheory.Functor Opposite
open ContentCovariantGrothendieck
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B]

def coy (A : B) : B ⥤ Cat.{u,u} := coyoneda.obj (op A) ⋙ typeToCat

def run {A D : B} : (Discrete (op D ⟶ op A))ᵒᵖ ⥤ Discrete (A ⟶ D) where
  obj x := Discrete.mk x.unop.as.unop
  map s := eqToHom (congrArg (fun x : op D ⟶ op A => Discrete.mk x.unop) (Discrete.eq_of_hom s.unop).symm)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def quote {A D : B} : Discrete (A ⟶ D) ⥤ (Discrete (op D ⟶ op A))ᵒᵖ where
  obj x := op (Discrete.mk x.as.op)
  map s := eqToHom (congrArg (fun x : A ⟶ D => op (Discrete.mk x.op)) (Discrete.eq_of_hom s))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem discreteFunExt {X Y : Type u} [Category.{u} X] [Category.{u} Y]
    [∀ a b : Y, Subsingleton (a ⟶ b)] {F G : X ⥤ Y} (h : ∀ x, F.obj x = G.obj x) : F = G :=
  Functor.ext h (by intros; exact Subsingleton.elim _ _)

def chartAt (A D : B) : (decode (RepresentableYoneda.rep (op A))).obj D ≅ (coy A).obj D where
  hom := (run (A := A) (D := D)).toCatHom
  inv := (quote (A := A) (D := D)).toCatHom
  hom_inv_id := by
    change (run (A := A) (D := D) ⋙ quote).toCatHom = (𝟭 _).toCatHom
    exact congrArg Functor.toCatHom (discreteFunExt (fun _ => rfl))
  inv_hom_id := by
    change (quote (A := A) (D := D) ⋙ run).toCatHom = (𝟭 _).toCatHom
    exact congrArg Functor.toCatHom (discreteFunExt (fun _ => rfl))

/-- The dual representable decodes to the actual discrete-valued coyoneda,
naturally in its covariant argument, not just a per-object type family. -/
def chart (A : B) : decode (RepresentableYoneda.rep (op A)) ≅ coy A :=
  NatIso.ofComponents (chartAt A) (by
    intro D E f
    change (((decode (RepresentableYoneda.rep (op A))).map f).toFunctor ⋙ run).toCatHom =
      (run ⋙ ((coy A).map f).toFunctor).toCatHom
    exact congrArg Functor.toCatHom (discreteFunExt (Y := Discrete (A ⟶ E)) (fun _ => rfl)))

end ContextualComposition.GrothendieckStep.ContentCorepresentableChart
