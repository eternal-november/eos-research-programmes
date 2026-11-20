module
public import ContextualComposition.ContextadRepresentable
public import ContextualComposition.BlockEvaluation
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComma
open CategoryTheory CategoryTheory.Functor Opposite ContextadRepresentable
set_option backward.isDefEq.respectTransparency false
universe b u
variable {B : Type b} [Category.{u} B] {K : Type u} [Category.{u} K] (e : K ⥤ B) (D : B)
abbrev Row := Total (rep D) e
abbrev Native := CostructuredArrow e D
def body (x : Row e D) : e.obj (grade _ _ x) ⟶ D := (payload (rep D) e x).as
theorem triangle {x y : Row e D} (h : x ⟶ y) : e.map (gradeMap h) ≫ body e D y = body e D x :=
  (Discrete.eq_of_hom (payloadMap h)).symm
theorem thinHEq {A : Type*} {C : A → Type*} [∀ a, Subsingleton (C a)] {i j : A}
    (e : i = j) (f : C i) (g : C j) : HEq f g := by subst j; exact heq_of_eq (Subsingleton.elim _ _)
theorem arrowExt {x y : Row e D} (h k : x ⟶ y) (w : gradeMap h = gradeMap k) : h = k := by
  apply (homEquiv x y).injective
  apply Sigma.ext w
  exact @thinHEq _ (fun g => (payload (rep D) e x : Discrete (e.obj (grade _ _ x) ⟶ D)) ⟶ Discrete.mk (e.map g ≫ body e D y)) (fun _ => Discrete.instSubsingletonDiscreteHom _ _) _ _ w (payloadMap h) (payloadMap k)
def read : Row e D ⥤ Native e D where
  obj x := CostructuredArrow.mk (body e D x)
  map h := CostructuredArrow.homMk (gradeMap h) (triangle e D h)
  map_id x := by ext; rfl
  map_comp h k := by ext; rfl
def write : Native e D ⥤ Row e D where
  obj x := pair (rep D) e x.left (Discrete.mk x.hom)
  map h := arrow h.left (eqToHom (congrArg Discrete.mk (CostructuredArrow.w h).symm))
  map_id x := by apply arrowExt e D; rfl
  map_comp h k := by apply arrowExt e D; rfl
theorem readWriteObj (x : Native e D) : (read e D).obj ((write e D).obj x) = x := by
  obtain ⟨k,⟨⟨⟩⟩,f⟩ := x
  rfl
theorem writeReadObj (x : Row e D) : (write e D).obj ((read e D).obj x) = x := rfl
theorem read_write : read e D ⋙ write e D = 𝟭 _ := by
  fapply Functor.ext
  · exact writeReadObj e D
  · intro x y f
    simpa only [Functor.id_map,eqToHom_refl,Category.id_comp,Category.comp_id] using arrowExt e D ((read e D ⋙ write e D).map f) f rfl
theorem written_cast {x y : Native e D} (h : x = y) : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by subst y; rfl
theorem write_read : write e D ⋙ read e D = 𝟭 _ := by
  fapply Functor.ext
  · exact readWriteObj e D
  · intro x y f
    ext
    simp only [Functor.id_map,eqToHom_refl,Category.id_comp,Category.comp_id]
    rfl
def iso : CategoryTheory.IsoCat (Row e D) (Native e D) where
  functor := read e D
  inverse := write e D
  unit_eq := (read_write e D).symm
  counit_eq := write_read e D
end ContextualComposition.GrothendieckStep.RepresentableComma
