import Mathlib

namespace SwarmPledge

structure State where
  hold : Bool
  terminal : Bool
  deriving DecidableEq

inductive Event where
  | applied | fenced | receipt | other
  deriving DecidableEq

def next (s : State) : Event → State
  | .applied | .fenced => {s with terminal := true}
  | .receipt => {s with hold := s.hold && !s.terminal}
  | .other => s

def Valid (s : State) : Prop := s.terminal = false → s.hold = true

theorem step_preserves (s : State) (a : Event) (h : Valid s) : Valid (next s a) := by
  rcases s with ⟨hold,term⟩
  cases hold <;> cases term <;> cases a <;> simp_all [Valid,next]

def initial : State := ⟨true,false⟩

theorem valid_trace (es : List Event) : Valid (es.foldl next initial) := by
  have aux : ∀ (s : State) (xs : List Event), Valid s → Valid (xs.foldl next s) := by
    intro s xs
    induction xs generalizing s with
    | nil => exact id
    | cons a xs ih =>
      intro hs
      exact ih (next s a) (step_preserves s a hs)
  exact aux initial es (by simp [initial,Valid])

def forgetTerminal (s : State) : State := {s with terminal := false}
def forgetHold (s : State) : State := {s with hold := false}

theorem terminal_amnesia_invalidates :
    ¬ Valid (forgetTerminal (next (next initial .fenced) .receipt)) := by
  simp [Valid,next,initial,forgetTerminal]

theorem hold_amnesia_invalidates : ¬ Valid (forgetHold initial) := by
  simp [Valid,initial,forgetHold]

-- Without terminal evidence, a decision depending only on the local holding
-- observation cannot distinguish a pending consumer from a closed one.
theorem silent_safe_rule_cannot_return (permits : Bool → Bool)
    (safe : ∀ s : State, Valid s → s.terminal = false → permits s.hold = false) :
    permits (next initial .fenced).hold = false := by
  exact safe initial (by simp [initial,Valid]) rfl

#print axioms step_preserves
#print axioms valid_trace
#print axioms terminal_amnesia_invalidates
#print axioms hold_amnesia_invalidates
#print axioms silent_safe_rule_cannot_return
end SwarmPledge
