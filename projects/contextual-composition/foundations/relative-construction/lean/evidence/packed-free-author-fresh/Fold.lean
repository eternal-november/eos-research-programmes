import ContextualComposition.PackedFree
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
namespace FoldProbe
set_option maxHeartbeats 1000000
abbrev Base := Discrete Unit
def star : Base := ⟨()⟩
def P : Endpoints.{0,0,0,0} Base where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend _ := (Functor.const _).obj star
  lift _ := 𝟙 _
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := by apply heq_of_eq; apply Subsingleton.elim
abbrev Y : Baseᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Nat)
def algebraAt (a : Baseᵒᵖ) : Total Y (P.extend a.unop) ⥤ Nat where
  obj x := 2*(show Nat from payload _ _ x) + (show Nat from grade _ _ x)
  map {x y} f := homOfLE <| Nat.add_le_add
    (Nat.mul_le_mul_left 2 (leOfHom (show (payload Y _ x : Nat) ⟶ (payload Y _ y : Nat) from payloadMap f)))
    (leOfHom (show (grade Y _ x : Nat) ⟶ (grade Y _ y : Nat) from gradeMap f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
def algebra : (PackedFree.step S).obj Y ⟶ Y where
  app a := (algebraAt a).toCatHom
  naturality a b f := by
    apply congrArg Functor.toCatHom
    fapply Functor.ext
    · intro x; rfl
    · intro x y g; exact @Subsingleton.elim _ (inferInstanceAs (Subsingleton ((_ : Nat) ⟶ (_ : Nat)))) _ _
def word (i j leaf : Nat) : (PackedFree.pow S Y 2).obj (op star) :=
  pair _ _ i (pair _ _ j leaf)
def value := ((PackedFree.fold S algebra (𝟙 Y)).app (op star)).toFunctor
-- A change of accumulation order would interchange these results.
example : value.obj ⟨2,word 1 3 5⟩ = (27:Nat) := rfl
example : value.obj ⟨2,word 3 1 5⟩ = (25:Nat) := rfl
example : value.obj ⟨0,(5:Nat)⟩ = (5:Nat) := rfl
example (k : (PackedFree.free S).obj Y ⟶ Y)
    (h : PackedFree.HomLaw S (PackedFree.cons S Y) algebra k)
    (h₀ : PackedFree.inc S Y 0 ≫ k = 𝟙 Y) : k = PackedFree.fold S algebra (𝟙 Y) :=
  (PackedFree.unique S algebra k h).trans (congrArg (PackedFree.fold S algebra) h₀)
#check PackedFree.join_summand S Y 0 3
#check PackedFree.join_summand S Y 3 0
#check (PackedFree.monad S).assoc Y
end FoldProbe
