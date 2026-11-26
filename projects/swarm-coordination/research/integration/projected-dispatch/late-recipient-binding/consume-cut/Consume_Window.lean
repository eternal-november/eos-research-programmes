import Mathlib

namespace ConsumeWindow

def earliest (receipt expiry : ℕ) (blocked : Bool) : ℕ :=
  if blocked then max receipt (expiry+1) else receipt

theorem exact_cut (r e t : ℕ) (blocked : Bool) :
    earliest r e blocked ≤ t ↔ r ≤ t ∧ (blocked = false ∨ e < t) := by
  cases blocked <;> simp [earliest]

theorem exact_deadline (r e due : ℕ) (blocked : Bool) :
    (∃ t, r ≤ t ∧ (blocked = false ∨ e < t) ∧ t ≤ due) ↔
    earliest r e blocked ≤ due := by
  constructor
  · rintro ⟨t,hr,hb,hd⟩
    exact le_trans ((exact_cut _ _ _ _).2 ⟨hr,hb⟩) hd
  · intro h
    have hh := (exact_cut r e (earliest r e blocked) blocked).1 le_rfl
    exact ⟨_, hh.1, hh.2, h⟩

theorem part_of_due_work (cap old later : ℕ)
    (overflow : cap < old+later) :
    ¬ (old+later ≤ cap ∨ later+old ≤ cap) := by omega

#print axioms exact_cut
#print axioms exact_deadline
#print axioms part_of_due_work
end ConsumeWindow
