import Mathlib

namespace CoveredCorridor
def NoGap (a b q r : ℝ) : Prop := ¬ (a < q ∧ r < b)

theorem min_nogap (a b c d q r : ℝ)
    (h₁ : NoGap a b q r) (h₂ : NoGap c d q r) :
    NoGap (min a c) (min b d) q r := by
  rintro ⟨lo, hi⟩
  have hb : r < b := lt_of_lt_of_le hi (min_le_left b d)
  have hd : r < d := lt_of_lt_of_le hi (min_le_right b d)
  rcases le_total a c with h | h
  · rw [min_eq_left h] at lo
    exact h₁ ⟨lo, hb⟩
  · rw [min_eq_right h] at lo
    exact h₂ ⟨lo, hd⟩

theorem max_nogap (a b c d q r : ℝ)
    (h₁ : NoGap a b q r) (h₂ : NoGap c d q r) :
    NoGap (max a c) (max b d) q r := by
  rintro ⟨lo, hi⟩
  have ha : a < q := lt_of_le_of_lt (le_max_left a c) lo
  have hc : c < q := lt_of_le_of_lt (le_max_right a c) lo
  rcases le_total b d with h | h
  · rw [max_eq_right h] at hi
    exact h₂ ⟨hc, hi⟩
  · rw [max_eq_left h] at hi
    exact h₁ ⟨ha, hi⟩
end CoveredCorridor
#print axioms CoveredCorridor.min_nogap
#print axioms CoveredCorridor.max_nogap
