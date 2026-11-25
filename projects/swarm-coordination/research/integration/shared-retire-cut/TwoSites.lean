import Mathlib

inductive Site where
  | left | right deriving DecidableEq

def alternative (s : Site) : Site :=
  match s with | .left => .right | .right => .left

def admissible (blocked : Site) (choice : Option Site) : Prop :=
  ∃ s, choice = some s ∧ s ≠ blocked

theorem no_uniform_choice (pick : Option Site) :
    ¬ (∀ s, admissible s pick) := by
  intro h
  cases pick with
  | none =>
      obtain ⟨s, he, hn⟩ := h .left
      contradiction
  | some c =>
      obtain ⟨s, he, hn⟩ := h c
      have hs : c = s := Option.some.inj he
      exact hn hs.symm

theorem actual_observation_suffices (s : Site) :
    admissible s (some (alternative s)) := by
  cases s <;> simp [admissible, alternative]

#print axioms no_uniform_choice
#print axioms actual_observation_suffices
