import ContextualComposition.PackedFree
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
open PackedFree
namespace Algebra206
abbrev B := Discrete Unit
def star : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of (Discrete Bool))
  extend _ := (Functor.const _).obj star
  lift _ := 𝟙 _
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := by apply heq_of_eq; apply Subsingleton.elim
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Bool))
abbrev Z : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Nat)
def action (b : Bool) (x : Nat) := if b then 3*x else x+1
theorem mono (b : Bool) {i j : Nat} (h : i ≤ j) : action b i ≤ action b j := by
  cases b <;> simp only [action, Bool.false_eq_true, ↓reduceIte] <;> omega
def algAt (A : Bᵒᵖ) : Total Z (P.extend A.unop) ⥤ Nat where
  obj x := action (show Discrete Bool from grade _ _ x).as (payload _ _ x)
  map {x y} f := homOfLE (by
    have e := Discrete.eq_of_hom (X := (grade Z _ x : Discrete Bool)) (Y := (grade Z _ y : Discrete Bool)) (gradeMap f)
    change action _ _ ≤ action _ _
    rw [e]
    exact mono _ (leOfHom (show (payload Z _ x : Nat) ⟶ payload Z _ y from payloadMap f)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
def alg : (step S).obj Z ⟶ Z where
  app a := (algAt a).toCatHom
  naturality _ _ _ := by
    apply congrArg Functor.toCatHom; fapply Functor.ext
    · intro x; rfl
    · intro x y f; exact @Subsingleton.elim _ (inferInstanceAs (Subsingleton ((_ : Nat) ⟶ (_ : Nat)))) _ _
def seedF : Discrete Bool ⥤ Nat := Discrete.functor (fun b : Bool => if b then 8 else 5)
def seed : Y ⟶ Z where
  app _ := seedF.toCatHom
  naturality _ _ _ := rfl
def word (outer inner x : Bool) : (pow S Y 2).obj (op star) := pair _ _ (Discrete.mk outer)
  (pair _ _ (Discrete.mk inner) (Discrete.mk x))
def f := ((foldEquiv S alg).symm seed).val
example : ((f.app (op star)).toFunctor.obj ⟨2,word false true false⟩ : Nat) = (16:Nat) := rfl
example : ((f.app (op star)).toFunctor.obj ⟨2,word true false false⟩ : Nat) = (18:Nat) := rfl
example : ((f.app (op star)).toFunctor.obj ⟨0,Discrete.mk true⟩ : Nat) = (8:Nat) := rfl
example (h : (free S).obj Y ⟶ Z) (hh : HomLaw S (cons S Y) alg h) (hz : inc S Y 0 ≫ h = seed) :
    h = f := (unique S alg h hh).trans (congrArg (fold S alg) hz)
example : (monad S).toFunctor = ChainPayload.iterateConstruction S := rfl
example : (monad S).η.app Y = inc S Y 0 := rfl
example : (generator S).app Y = inc S Y 1 := rfl
example : (monad S).μ.app Y = fold S (cons S Y) (𝟙 _) := rfl
example : (generator S).app Y ≫ fold S alg seed = (step S).map seed ≫ alg := inc_fold S alg seed 1
end Algebra206
