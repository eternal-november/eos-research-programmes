import Mathlib
namespace SenderRx
def both (carry a b ca cb : Nat) : Prop :=
  carry + a ≤ ca ∧ carry + a + b ≤ cb

theorem invert_adjacent (carry a b ca cb : Nat)
    (caps : cb ≤ ca) (ab : both carry a b ca cb) :
    both carry b a cb ca := by
  unfold both at *
  omega

theorem invisible_supplier :
    both 0 173 60 200 233 ∧ ¬ both 0 60 173 233 200 ∧
    both 0 60 173 200 233 ∧ ¬ both 0 173 60 233 200 := by unfold both; decide

theorem joint_blind (c : Nat) :
    (both 0 173 60 c 233 ∧ both 0 173 60 233 c) ↔ 233 ≤ c := by
  unfold both
  omega

theorem robust_prefix (d c1 c2 : Nat) :
    (d ≤ c1 ∧ d ≤ c2) ↔ d ≤ min c1 c2 := by omega

#print axioms invert_adjacent
#print axioms invisible_supplier
#print axioms joint_blind
#print axioms robust_prefix
end SenderRx
