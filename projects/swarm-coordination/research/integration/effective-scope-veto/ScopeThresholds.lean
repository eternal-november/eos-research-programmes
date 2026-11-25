import Mathlib
namespace ScopeThresholds

def admitted {A : Type} (p : A → ℕ) (t : ℕ) : Set A :=
    {a | t ≤ p a}

theorem nested {A : Type} (p : A → ℕ) (s t : ℕ) :
    admitted p s ⊆ admitted p t ∨ admitted p t ⊆ admitted p s := by
  rcases le_total s t with h|h
  · right
    intro a ha
    exact le_trans h ha
  · left
    intro a ha
    exact le_trans h ha

theorem cannot_choose_two_isolated_directions (p : Bool → ℕ) (s t : ℕ)
    (left : admitted p s = {true}) (right : admitted p t = {false}) : False := by
  have h := nested p s t
  rw [left, right] at h
  rcases h with h|h
  · have bad : true ∈ ({false} : Set Bool) := h (by simp)
    simp at bad
  · have bad : false ∈ ({true} : Set Bool) := h (by simp)
    simp at bad

#print axioms nested
#print axioms cannot_choose_two_isolated_directions
end ScopeThresholds
