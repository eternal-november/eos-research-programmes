import Mathlib
namespace EventWindow

theorem noPointOverlap (a b l u : Nat) (ab : a < b) (lu : l < u) :
    (∀ t : Nat, a ≤ t → t < b → ¬ (l ≤ t ∧ t < u))
       ↔ (b ≤ l ∨ u ≤ a) := by
  constructor
  · intro h
    by_contra! h'
    have H := h (max a l) (by omega) (by omega)
    exact H ⟨by omega, by omega⟩
  · intro h t h0 h1
    rcases h with h | h <;> omega

theorem endCutIsNotConsumed (a b u : Nat) :
    ∀ t : Nat, a ≤ t → t < b → ¬ (b ≤ t ∧ t < u) := by omega
end EventWindow
#print axioms EventWindow.noPointOverlap
#print axioms EventWindow.endCutIsNotConsumed
