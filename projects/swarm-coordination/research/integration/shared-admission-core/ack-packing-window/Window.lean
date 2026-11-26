import Lean
namespace Preludes

theorem carry_exact (tx rx : Nat) :
    (2+tx+2≤5 ∧ 2+rx+2≤5) ↔ tx≤1 ∧ rx≤1 := by omega

theorem no_joint_send_between (available cut : Nat) :
    (∃ send : Nat, available≤send ∧ send≤cut) ↔ available≤cut := by
  constructor
  · rintro ⟨t,ha,hc⟩
    omega
  · intro h
    exact ⟨available,Nat.le_refl _,h⟩

theorem same_late_fields_not_same_prefix (clear deadline : Nat)
    (tight : clear=deadline) :
    clear≤deadline ∧ ¬clear+1≤deadline := by
  omega

theorem one_byte_shared_on_each_side :
    (2+1+2≤5) ∧ ¬(2+1+1+2≤5) := by decide

#print axioms carry_exact
#print axioms no_joint_send_between
#print axioms same_late_fields_not_same_prefix
#print axioms one_byte_shared_on_each_side
end Preludes
