import ContextualComposition.StrictTelAlgebra
open CategoryTheory ContextualComposition.GrothendieckStep
open NativeBlocks NativeBlocks.Nested StrictTelAlgebra
namespace StrictTelNativeObstruction
inductive Token where | leaf
instance : Category.{0} Token where
  Hom _ _ := Nat
  id _ := 0
  comp a b := a + b
  id_comp := by intros; apply Nat.zero_add
  comp_id := by intros; apply Nat.add_zero
  assoc := by intros; apply Nat.add_assoc
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Token)
  extend A := (Functor.const Token).obj (A+1)
  lift u := { app := fun _ => homOfLE (Nat.succ_le_succ (leOfHom u)) }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
def shiftEdge : (0:Nat) ⟶ 1 := homOfLE (by decide)
theorem noReverse : ¬ Nonempty ((1:Nat) ⟶ 0) :=
  fun ⟨f⟩ => (by decide : ¬ (1:Nat) ≤ 0) (leOfHom f)
/-- There cannot even be a functor action strict over both endpoints. The
empty word is a 0-to-0 arrow, and every primitive extends by one. -/
theorem noNativeAction : ¬ Nonempty (Over (whole S) (power S 1)) := by
  rintro ⟨A⟩
  let x := (incl S 0).obj (0:Nat)
  let z := A.functor.obj x
  have h := Functor.congr_obj A.dest x
  change (grade P.grades (𝟭 Nat) z)+1 = 0 at h
  exact Nat.noConfusion h
theorem noAlgebra : ¬ Nonempty (Algebra S) := fun ⟨A⟩ => noNativeAction ⟨A.action⟩
end StrictTelNativeObstruction
#print axioms StrictTelNativeObstruction.noAlgebra
