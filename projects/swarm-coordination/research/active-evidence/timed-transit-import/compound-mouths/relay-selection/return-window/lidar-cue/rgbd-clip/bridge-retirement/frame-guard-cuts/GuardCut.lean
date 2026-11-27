import Mathlib

namespace GuardCut
/-- At all cuts of a legal alternating path, a repeated visible (bit, tag)
    would make exact no-transition checking impossible across that pair. -/
theorem minimum_tags (H M : Nat) (tag : Nat → Fin M)
    (fresh : ∀ i j : Nat, i ≤ H → j ≤ H →
      i % 2 = j % 2 → tag i = tag j → i = j) :
    H / 2 + 1 ≤ M := by
  let e : Fin (H/2 + 1) → Fin M := fun i => tag (2 * i.val)
  have hi : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have a : 2 * i.val ≤ H := by have := i.isLt; omega
    have b : 2 * j.val ≤ H := by have := j.isLt; omega
    have eq : 2 * i.val = 2 * j.val := fresh _ _ a b (by omega) hij
    omega
  simpa using Fintype.card_le_of_injective e hi

theorem half_counter_size (H : Nat) : H < 2 * (H / 2 + 1) := by omega

theorem nonzero_gap_visible (M k : Nat) (hk : k < 2 * M)
    (hc : k % (2 * M) = 0) : k = 0 := by
  rwa [Nat.mod_eq_of_lt hk] at hc

theorem wrap_when_unbounded (M : Nat) (hp : 0 < M) :
    0 < 2 * M ∧ (2 * M) % (2 * M) = 0 := by
  exact ⟨by omega, Nat.mod_self _⟩

theorem flip_step (q b M : Nat) 
    (hb : b ≤ 1) :
    (2 * (q + b) + (1 - b)) % (2 * M) = (2*q + b + 1) % (2*M) := by
  have e : 2 * (q + b) + (1 - b) = 2*q + b + 1 := by omega
  rw [e]

#print axioms minimum_tags
#print axioms half_counter_size
#print axioms nonzero_gap_visible
#print axioms wrap_when_unbounded
#print axioms flip_step
end GuardCut
