import Mathlib
namespace OrderedReuse

-- True marks an already held segment that can be accepted on its own.
-- The parameter marks whether an empty carrier is currently available.
def serial : Bool → List Bool → Prop
  | _, [] => True
  | available, kept :: rest => (kept = true ∨ available = true) ∧ serial true rest

theorem after_first (xs : List Bool) : serial true xs := by
  induction xs with
  | nil => trivial
  | cons k rest ih => exact ⟨Or.inr rfl, ih⟩

theorem exact_front (available kept : Bool) (rest : List Bool) :
    serial available (kept :: rest) ↔ (kept = true ∨ available = true) :=
  ⟨fun h => h.1, fun h => ⟨h, after_first rest⟩⟩

theorem held_prefix_supplies_one (rest : List Bool) : serial false (true :: rest) :=
  (exact_front false true rest).2 (Or.inl rfl)

theorem leading_gap_still_blocks (rest : List Bool) : ¬serial false (false :: rest) := by
  intro h
  have q := (exact_front false false rest).1 h
  cases q with
  | inl h => cases h
  | inr h => cases h
end OrderedReuse

#print axioms OrderedReuse.exact_front
#print axioms OrderedReuse.held_prefix_supplies_one
#print axioms OrderedReuse.leading_gap_still_blocks
