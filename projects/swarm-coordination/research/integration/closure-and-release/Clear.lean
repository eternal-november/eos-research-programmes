import Mathlib

def after (occupancy : Bool) (actions : List (Bool × Bool)) : Bool :=
  actions.foldl (fun busy (entry, depart) => entry || (busy && !depart)) occupancy

theorem no_entry_preserves_empty (actions : List (Bool × Bool))
    (h : ∀ a ∈ actions, a.1 = false) :
    after false actions = false := by
  induction actions with
  | nil => rfl
  | cons a rest ih =>
    rcases a with ⟨entry, depart⟩
    have ha : entry = false := h (entry, depart) (by simp)
    have hr : ∀ b ∈ rest, b.1 = false := by
      intro b hb
      exact h b (by simp [hb])
    simpa [after, ha] using ih hr

theorem open_entry_can_defeat_cached_clearance (pre post : List (Bool × Bool))
    (h : ∀ a ∈ post, a = (false, false)) :
    after false (pre ++ (true, false) :: post) = true := by
  have hold : ∀ l : List (Bool × Bool),
      (∀ a ∈ l, a = (false, false)) → after true l = true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a rest ih =>
      rw [hl a (by simp)]
      have hr : ∀ b ∈ rest, b = (false, false) := by
        intro b hb
        exact hl b (by simp [hb])
      simpa [after] using ih hr
  simp [after, List.foldl_append]
  simpa [after] using hold post h

#print axioms no_entry_preserves_empty
#print axioms open_entry_can_defeat_cached_clearance
