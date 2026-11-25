import Mathlib

namespace RestartValidation

theorem isolation_gain {x y u d h : ℝ} (hu : 0 < u) (hd : 0 ≤ d) :
    max (x+u+d) y+h < max x y+u+h ↔ d < y-x := by
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy]
    constructor
    · intro hc
      have hb := le_max_left (x+u+d) y
      linarith
    · intro hh
      by_cases hq : x+u+d ≤ y
      · rw [max_eq_right hq]; linarith
      · rw [max_eq_left (le_of_not_ge hq)]; linarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [max_eq_left hyx, max_eq_left (show y ≤ x+u+d by linarith)]
    constructor <;> intro hh <;> linarith

theorem isolation_gain_size {x y u d h : ℝ} (hd : 0 ≤ d) (gain : d < y-x) :
    (max x y+u+h)-(max (x+u+d) y+h) = min u (y-x-d) := by
  have hxy : x ≤ y := by linarith
  rw [max_eq_right hxy]
  by_cases hq : x+u+d ≤ y
  · rw [max_eq_right hq, min_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge hq), min_eq_right (by linarith)]
    ring

theorem shared_lower {x y u h started tested finished : ℝ}
    (xstart : x ≤ started) (ystart : y ≤ started)
    (test : started+u ≤ tested) (job : tested+h ≤ finished) :
    max x y+u+h ≤ finished := by
  have hxy := max_le xstart ystart
  linarith

theorem isolated_lower {x y u d h started reply issued finished : ℝ}
    (xstart : x ≤ started) (receipt : started+u+d ≤ reply)
    (yissued : y ≤ issued) (rissued : reply ≤ issued) (job : issued+h ≤ finished) :
    max (x+u+d) y+h ≤ finished := by
  have hxy : max (x+u+d) y ≤ issued := max_le (by linarith) yissued
  linarith

end RestartValidation
#print axioms RestartValidation.isolation_gain
#print axioms RestartValidation.isolation_gain_size
#print axioms RestartValidation.shared_lower
#print axioms RestartValidation.isolated_lower
