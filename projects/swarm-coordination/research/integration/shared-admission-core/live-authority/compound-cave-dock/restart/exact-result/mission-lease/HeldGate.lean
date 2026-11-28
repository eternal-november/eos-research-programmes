import Mathlib
namespace HeldGate

-- The source adapter must derive the set of times for which the
-- chosen body's envelope touches the gate that is currently open.
def covers (touched : Set ℝ) (ends : ℝ) : Prop :=
  ∀ t ∈ touched, t ≤ ends

theorem exact (touched : Set ℝ) (last ends : ℝ)
    (attained : last ∈ touched) (bound : ∀ t ∈ touched, t ≤ last) :
    covers touched ends ↔ last ≤ ends := by
  constructor
  · intro h
    exact h last attained
  · intro h t ht
    exact le_trans (bound t ht) h

theorem shift (touched : Set ℝ) (d ends : ℝ) :
    covers ((fun t => t+d) '' touched) ends ↔ covers touched (ends-d) := by
  constructor
  · intro h t ht
    have v := h (t+d) ⟨t,ht,rfl⟩
    linarith
  · rintro h u ⟨t,ht,rfl⟩
    have v := h t ht
    linarith

-- Binary-exact slots of 1/16 s; preselected source model, not transport.
theorem firstPossibleAfterDebit (h : ℕ) (expired : 29 < h) : 30 ≤ h := by omega

end HeldGate
#print axioms HeldGate.exact
#print axioms HeldGate.shift
#print axioms HeldGate.firstPossibleAfterDebit
