import Mathlib

namespace HandoffCut

theorem no_overlap {W : Type} (d latency : W → ℤ) (qualified : W → Prop)
    [DecidablePred qualified] (x : ℤ) (h : ∀ w, 0 ≤ latency w) :
    (∀ w, 0 ≤ if qualified w then min (x - d w) (latency w) else x - d w) ↔
    ∀ w, d w ≤ x := by
  constructor
  · intro hh w
    by_cases he : qualified w
    · have hp : 0 ≤ min (x - d w) (latency w) := by simpa [he] using hh w
      have hq := le_trans hp (min_le_left (x - d w) (latency w))
      omega
    · have hp : 0 ≤ x - d w := by simpa [he] using hh w
      omega
  · intro hh w
    have hp : 0 ≤ x - d w := by have hw := hh w; omega
    by_cases he : qualified w
    · rw [ite_eq_left he]
      exact le_min hp (h w)
    · rw [ite_eq_right he]
      exact hp

theorem earliest_minimizes {W : Type} (d latency : W → ℤ) (qualified : W → Prop)
    [DecidablePred qualified] (x y : ℤ) (h : x ≤ y) (w : W) :
    (if qualified w then min (x-d w) (latency w) else x-d w) ≤
    (if qualified w then min (y-d w) (latency w) else y-d w) := by
  by_cases he : qualified w
  · rw [ite_eq_left he, ite_eq_left he]
    exact min_le_min (by omega) le_rfl
  · rw [ite_eq_right he, ite_eq_right he]
    omega

end HandoffCut

#print axioms HandoffCut.no_overlap
#print axioms HandoffCut.earliest_minimizes
