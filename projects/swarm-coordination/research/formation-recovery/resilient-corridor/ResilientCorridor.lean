import Mathlib

namespace ResilientCorridor

theorem upper_max (a b c d r : ℝ) (hab : b ≤ a+r) (hcd : d ≤ c+r) :
    max b d ≤ max a c+r := by
  apply max_le
  · have H := le_max_left a c
    linarith
  · have H := le_max_right a c
    linarith

theorem upper_min (a b c d r : ℝ) (hab : b ≤ a+r) (hcd : d ≤ c+r) :
    min b d ≤ min a c+r := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
    exact (min_le_left b d).trans hab
  · rw [min_eq_right h]
    exact (min_le_right b d).trans hcd

theorem moving_toward_cut_improves_gap (L L' R R' g : ℝ)
    (hL : L ≤ L') (hR : R' ≤ R) (h : R-L ≤ g) : R'-L' ≤ g := by
  linarith

theorem survives_every_k {α : Type} [DecidableEq α] (I : Finset α) (k : ℕ) :
    (∀ D : Finset α, D.card ≤ k → ∃ i ∈ I, i ∉ D) ↔ k < I.card := by
  constructor
  · intro h
    by_contra! he
    obtain ⟨i,hin,hnot⟩ := h I he
    contradiction
  · intro h D hD
    by_contra! hn
    have hs : I ⊆ D := fun i hi => hn i hi
    have hc := Finset.card_le_card hs
    omega

theorem lens (a b z r : ℝ) :
    (z-a ≤ r ∧ b-z ≤ r) ↔ (b-r ≤ z ∧ z ≤ a+r) := by
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

end ResilientCorridor
#print axioms ResilientCorridor.upper_max
#print axioms ResilientCorridor.upper_min
#print axioms ResilientCorridor.moving_toward_cut_improves_gap
#print axioms ResilientCorridor.survives_every_k
#print axioms ResilientCorridor.lens
