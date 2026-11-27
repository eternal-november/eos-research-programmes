import Mathlib

namespace ChargedEvidence

def debit (stamp tick : Nat) : Nat :=
  if tick ≤ stamp + 4 then 1 else 0

theorem live_at_boundary (t : Nat) : debit t (t+4) = 1 := by
  simp [debit]

theorem expired_beyond_boundary (t : Nat) : debit t (t+5) = 0 := by
  unfold debit
  split <;> omega

theorem reverse_impossible (d : Nat) : ¬ (d + 3 + 2 ≤ 4) := by omega

theorem same_cut_iff (stamp tick w : Nat) :
    ((debit stamp tick + 2 ≤ 4) ∧
     (debit stamp tick + 2 + 3 ≤ 5 + w)) ↔
    stamp + 4 < tick ∨ 1 ≤ w := by
  unfold debit
  split <;> omega

theorem split_cut_iff (stamp first second w : Nat) (h : second ≤ first+4) :
    ((debit stamp first + 2 ≤ 4) ∧
      (debit first second * 2 + debit stamp second + 3 ≤ 5+w)) ↔
    stamp + 4 < second ∨ 1 ≤ w := by
  unfold debit
  by_cases hd : second ≤ stamp + 4 <;> by_cases hf : first ≤ stamp + 4 <;>
    simp [h, hd, hf] <;> omega

theorem window_bare_reply_not_enough (prior notice : Nat)
    (hp : prior=2) (hn : notice=1) :
    ¬ (prior+notice+3 ≤ 5) := by omega

#print axioms live_at_boundary
#print axioms expired_beyond_boundary
#print axioms reverse_impossible
#print axioms same_cut_iff
#print axioms split_cut_iff
#print axioms window_bare_reply_not_enough
end ChargedEvidence
