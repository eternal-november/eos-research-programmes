import Mathlib

namespace DoorEffect

def debit (k j : Nat) := k - j

def dipUnits : Nat → Nat
  | 0 => 0
  | k + 1 => dipUnits k + k

theorem accumulated_residual (k : Nat) :
    2 * dipUnits k = k * (k - 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [dipUnits]
    cases k with
    | zero => decide
    | succ h =>
      simp only [Nat.succ_sub_one] at ih ⊢
      nlinarith

theorem fixed_step_decay (k j : Nat) :
    debit k (j+1) = debit k j - 1 := by
  simp only [debit]
  omega

theorem threshold_witness :
    (2 * dipUnits 4 < 16) ∧ ¬ (2 * dipUnits 5 < 16) := by decide

end DoorEffect
