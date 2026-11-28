import Mathlib
namespace DoorTransfer

-- Units of 1/64 in velocity and 1/512 in distance.
-- This recurrence is restricted to the stated close/hold histories
-- and the modeled velocity-following continuation.
def speed (prior permitAfter : Nat) : Nat → Nat
  | 0 => prior - 1
  | n+1 => if 1 ≤ n+1 ∧ permitAfter ≤ n+1
      then min 16 (speed prior permitAfter n + 1)
      else speed prior permitAfter n - 1

def dip (prior permitAfter ticks : Nat) : Nat :=
  ∑ t ∈ Finset.range ticks, speed prior permitAfter t

theorem matched_boundary :
    dip 2 2 5 = 7 ∧ dip 2 1 5 = 15 ∧ dip 5 6 4 = 10 := by
  decide

theorem scope_matters :
    dip 2 2 5 < 8 ∧ ¬ dip 2 1 5 < 8 ∧ ¬ dip 5 6 4 < 8 := by
  decide

theorem paid_one_tick_of_observation (deadline : Nat) :
    (∃ wait : Nat, 1 + wait + 4 ≤ deadline) ↔ 5 ≤ deadline := by
  constructor
  · rintro ⟨wait,h⟩
    omega
  · intro h
    exact ⟨0,h⟩
end DoorTransfer
