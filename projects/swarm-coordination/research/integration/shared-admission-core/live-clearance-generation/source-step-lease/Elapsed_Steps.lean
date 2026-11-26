import Mathlib

namespace SwarmElapsed

def Safe (J : Nat → Nat → Prop) (firstReturn : Nat) : Prop :=
  ∀ a b, J a b → a + b < firstReturn

def shared (budget a b : Nat) : Prop := a + b = budget

def separate (budget a b : Nat) : Prop := a ≤ budget ∧ b ≤ budget

theorem exact_shared (H R : Nat) : Safe (shared H) R ↔ H < R := by
  constructor
  · intro h
    simpa using h H 0 (by simp [shared])
  · intro h a b hab
    change a + b = H at hab
    omega

theorem exact_rectangular (H R : Nat) :
    Safe (separate H) R ↔ H + H < R := by
  constructor
  · intro h
    exact h H H ⟨le_rfl, le_rfl⟩
  · intro h a b hab
    rcases hab with ⟨ha,hb⟩
    omega

theorem stagewise_maxima_erase_a_law :
    Safe (shared 2) 3 ∧ ¬ Safe (separate 2) 3 := by
  rw [exact_shared, exact_rectangular]
  decide

theorem adding_one_source_step_can_restore_slack :
    ¬ Safe (shared 3) 3 ∧ Safe (shared 3) 4 := by
  rw [exact_shared, exact_shared]
  decide

theorem at_first_return_is_not_strictly_safe (R : Nat) : ¬ Safe (shared R) R := by
  rw [exact_shared]
  exact lt_irrefl _

#print axioms exact_shared
#print axioms exact_rectangular
#print axioms stagewise_maxima_erase_a_law
#print axioms adding_one_source_step_can_restore_slack
#print axioms at_first_return_is_not_strictly_safe
end SwarmElapsed
