import Mathlib

namespace ReceiverFence

inductive Cut where
  | initial | acceptedOld | replacedAtA | stitchedAtB
  deriving DecidableEq

inductive Input where
  | release | replace | stitch
  deriving DecidableEq

def step : Cut → Input → Cut
  | .initial, .release => .acceptedOld
  | .initial, .replace => .replacedAtA
  | .acceptedOld, .stitch => .stitchedAtB
  | s, _ => s

def oldAccepted : Cut → Bool
  | .acceptedOld | .stitchedAtB => true
  | _ => false

theorem prior_survives (s : Cut) (a : Input) (old : oldAccepted s = true) :
    oldAccepted (step s a) = true := by
  cases s <;> cases a <;> simp_all [oldAccepted, step]

theorem survives_word (s : Cut) (xs : List Input) (old : oldAccepted s = true) :
    oldAccepted (xs.foldl step s) = true := by
  induction xs generalizing s with
  | nil => exact old
  | cons x xs ih =>
      exact ih (step s x) (prior_survives s x old)

theorem exact_replacement_excludes (s : Cut) (xs : List Input)
    (placed : xs.foldl step s = Cut.replacedAtA) : oldAccepted s = false := by
  cases h : oldAccepted s
  · rfl
  · have q := survives_word s xs h
    rw [placed] at q
    simp [oldAccepted] at q

#print axioms prior_survives
#print axioms survives_word
#print axioms exact_replacement_excludes
end ReceiverFence
