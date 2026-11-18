import ContextualComposition.EmptyUnitOverlap
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep BlockUnits EmptyUnitOverlap NativePacked NativeBlocks
namespace Coherent213
set_option backward.isDefEq.respectTransparency false
section Square
variable {Z X C D : Type*} [Category* Z] [Category* X] [Category* C] [Category* D]
variable (K : Z ⥤ X) (J : Side → X ⥤ C) (F : C ⥤ D) (T : Side → X ⥤ D)
variable (U : (s : Side) → J s ⋙ F ⟶ T s)
def commutes (p : K ⋙ J .left = K ⋙ J .right) (q : K ⋙ T .left = K ⋙ T .right) : Prop :=
  eqToHom (congrArg (· ⋙ F) p) ≫ whiskerLeft K (U .right) = whiskerLeft K (U .left) ≫ eqToHom q
theorem extensional (p : K ⋙ J .left = K ⋙ J .right) (q : K ⋙ T .left = K ⋙ T .right)
    (h : ∀ x, agreesAt J F T (fun s z => (U s).app z) (K.obj x) (Functor.congr_obj p x) (Functor.congr_obj q x)) :
    commutes K J F T U p q := by
  unfold commutes
  ext x
  simp only [NatTrans.comp_app,eqToHom_app,whiskerLeft_app]
  exact h x
end Square
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
noncomputable def U (s : Side) : J S Y A s ⋙ CutCompositor.stages S Y A ⟶ target S Y A s :=
  (stagedUnit S Y A s).hom
-- The instantiated conclusion is equality of natural transformations of
-- the actual empty-word fibre, not just equality at selected vertices.
example : commutes (empty S Y A) (J S Y A) (CutCompositor.stages S Y A) (target S Y A) (U S Y A)
    (degenerate S Y A) (atZero S Y A) :=
  extensional _ _ _ _ _ _ _ (overlap S Y A)
end Coherent213
