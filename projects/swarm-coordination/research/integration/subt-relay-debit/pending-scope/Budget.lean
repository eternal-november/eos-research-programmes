import Lean

namespace PendingRolling

theorem current_budget_not_enough (a b x c : Nat)
    (second_legal : a+b ≤ c) (new_legal : a+x ≤ c) (combined : c < a+b+x) :
    a+x ≤ c ∧ a+b ≤ c ∧ ¬ (a+x+b ≤ c) := by omega

theorem strict_expiry_releases (a b x c : Nat)
    (before_full : c < a+b+x) (after_first : b+x ≤ c) :
    ¬ (a+b+x ≤ c) ∧ b+x ≤ c := by omega

theorem asymmetric_alias : 2+2+2 ≤ (6:Nat) ∧ ¬ (2+2+2 ≤ (5:Nat)) := by decide

#print axioms current_budget_not_enough
#print axioms strict_expiry_releases
#print axioms asymmetric_alias

end PendingRolling
