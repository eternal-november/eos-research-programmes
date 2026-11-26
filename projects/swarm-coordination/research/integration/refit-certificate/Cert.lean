import Mathlib

/-- A linear clearance score at an interior point is between the endpoints. -/
theorem convex_score_preserves_bound (a b u v x y t threshold : ℚ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (left : threshold ≤ a*u + b*v) (right : threshold ≤ a*x + b*y) :
    threshold ≤ a*(t*u+(1-t)*x) + b*(t*v+(1-t)*y) := by
  have p := mul_le_mul_of_nonneg_left left h0
  have q := mul_le_mul_of_nonneg_left right (sub_nonneg.mpr h1)
  nlinarith

theorem same_marginals_different_score :
    min (1 : ℚ) 2 = min 1 2 ∧ min (2 : ℚ) 1 = min 1 2 ∧
    min ((1:ℚ)+2) (2+1) - 1/4 ≥ 5/2 ∧
    ¬ (min ((1:ℚ)+1) (2+2) - 1/4 ≥ 5/2) := by
  norm_num

#print axioms convex_score_preserves_bound
#print axioms same_marginals_different_score

theorem inserted_score_unchanged_iff (x y z : ℚ) :
    min (min x y) z = min x y ↔ min x y ≤ z := by
  exact min_eq_left_iff

#print axioms inserted_score_unchanged_iff
