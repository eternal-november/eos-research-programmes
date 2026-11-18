import Mathlib.CategoryTheory.Types.Basic
open CategoryTheory
namespace MovingSuffix
abbrev K := (Functor.const (Type)).obj (ULift.{1} Bool : Type 1)
-- Every displayed component is invertible. They cannot be the components of
-- one total cell: the crossing from the one-point to the two-point base forces
-- equality on the constant fibre.
example : ¬ ∃ t : K ⟶ K, (∀ z, (t.app PUnit) z = z) ∧
    (∀ z, (t.app Bool) z = ⟨!z.down⟩) := by
  rintro ⟨t,h,k⟩
  let f : PUnit ⟶ Bool := TypeCat.ofHom (fun _ => false)
  have n := congrArg (fun g : ULift.{1} Bool ⟶ ULift.{1} Bool => g ⟨false⟩) (t.naturality f)
  change (t.app Bool) ⟨false⟩ = (t.app PUnit) ⟨false⟩ at n
  rw [h,k] at n
  exact Bool.noConfusion (congrArg ULift.down n)
end MovingSuffix
