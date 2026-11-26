import Mathlib

namespace RestartGate

def copies (old retry : Bool) : Nat := old.toNat + retry.toNat

theorem noSameViewChoice (retry : Bool) :
    ¬ (copies false retry = 1 ∧ copies true retry = 1) := by
  cases retry <;> decide

theorem exactRead (oldPaid : Bool) :
    copies oldPaid (!oldPaid) = 1 := by
  cases oldPaid <;> decide

theorem exactReadDoesNotFence :
    copies true (!false) = 2 := by decide

/-- In the sink-local gate, a delivered attempt can consume only once. -/
def consume (paid attempt : Bool) := paid || attempt

def after (xs : List Bool) := xs.foldl consume false

theorem gateStateInduction (paid : Bool) (xs : List Bool) :
    xs.foldl consume paid = (paid || xs.any id) := by
  induction xs generalizing paid with
  | nil => cases paid <;> rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases x <;> cases paid <;> simp [consume]

theorem gateCoveredDeadline (old primary backup due : Nat)
    (hold : old ≤ due ∨ primary ≤ due ∨ backup ≤ due) :
    min old (min primary backup) ≤ due := by omega

end RestartGate

#print axioms RestartGate.noSameViewChoice
#print axioms RestartGate.exactRead
#print axioms RestartGate.exactReadDoesNotFence
#print axioms RestartGate.gateStateInduction
#print axioms RestartGate.gateCoveredDeadline
