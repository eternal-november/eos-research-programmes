import Mathlib

namespace SwarmRadioLens

theorem horizontal_extent {a R x : ℝ} (hR : 0 ≤ R)
    (h1 : (x+a)^2 ≤ R^2) (h2 : (x-a)^2 ≤ R^2) :
    -(R-a) ≤ x ∧ x ≤ R-a := by
  constructor
  · by_contra hh
    have h : x-a < -R := by linarith
    nlinarith [mul_pos (by linarith : 0 < -(x-a)-R) (by linarith : 0 < -(x-a)+R)]
  · by_contra hh
    have h : R < x+a := by linarith
    nlinarith [mul_pos (by linarith : 0 < x+a-R) (by linarith : 0 < x+a+R)]

theorem centered_crossing_blocked {a R rho x : ℝ}
    (hR : 0 ≤ R) (h : R-a < rho)
    (h1 : (x+a)^2 ≤ R^2) (h2 : (x-a)^2 ≤ R^2) :
    x^2 < rho^2 := by
  obtain ⟨hl,hr⟩ := horizontal_extent hR h1 h2
  have hA : 0 < rho - x := by linarith
  have hB : 0 < rho + x := by linarith
  nlinarith [mul_pos hA hB]

theorem reflected_crossing_blocked {a R rho c x : ℝ}
    (hR : 0 ≤ R) (hc : c < rho) (h : R-a < c+rho)
    (h1 : (x+a)^2 ≤ R^2) (h2 : (x-a)^2 ≤ R^2) :
    (x-c)^2 < rho^2 ∨ (x+c)^2 < rho^2 := by
  obtain ⟨hl,hr⟩ := horizontal_extent hR h1 h2
  by_cases H : 0 ≤ x
  · left
    have hA : 0 < rho-(x-c) := by linarith
    have hB : 0 < rho+(x-c) := by linarith
    nlinarith [mul_pos hA hB]
  · right
    have hA : 0 < rho-(x+c) := by linarith
    have hB : 0 < rho+(x+c) := by linarith
    nlinarith [mul_pos hA hB]

theorem far_side_arc_inside {a R rho c u y : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ rho) (hc : -a ≤ c) (ha : c ≤ a)
    (hu : u ≤ 0) (hcirc : u^2+y^2 = rho^2)
    (hFar : a-c+rho ≤ R) (hNear : (a+c)^2+rho^2 ≤ R^2) :
    (c+u+a)^2+y^2 ≤ R^2 ∧ (c+u-a)^2+y^2 ≤ R^2 := by
  have uu : -rho ≤ u := by
    by_contra h
    have h' : u < -rho := lt_of_not_ge h
    nlinarith [sq_nonneg y, mul_pos (by linarith : 0 < -u-rho)
      (by linarith : 0 < -u+rho)]
  constructor
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ a+c) hu]
  · have h1 := mul_nonpos_of_nonpos_of_nonneg (by linarith : c-a ≤ 0) (by linarith : 0 ≤ u+rho)
    have h2 := mul_nonneg (sub_nonneg.mpr hFar) (by linarith : 0 ≤ R + (a-c+rho))
    nlinarith

theorem right_half_blocked {a R rho c x : ℝ}
    (hR : 0 ≤ R) (hc : c < rho) (h : R-a < c+rho) (hx : 0 ≤ x)
    (h1 : (x+a)^2 ≤ R^2) (h2 : (x-a)^2 ≤ R^2) :
    (x-c)^2 < rho^2 := by
  have hmax := (horizontal_extent hR h1 h2).2
  have hA : 0 < rho-(x-c) := by linarith
  have hB : 0 < rho+(x-c) := by linarith
  nlinarith [mul_pos hA hB]

theorem central_stage_height {y c rho cap : ℝ}
    (hy : y ≤ 0) (hcap : cap^2 = rho^2-c^2)
    (hr : rho^2 ≤ c^2 + y^2) :
    cap ≤ -y := by
  by_contra h
  have h1 : 0 < cap+y := by linarith
  have h2 : 0 < cap-y := by linarith
  nlinarith [mul_pos h1 h2]

theorem later_cut_not_faster {r t m n v : ℝ} (h : m ≤ n+v*(t-r)) :
    v*r + m ≤ v*t + n := by linarith

#print axioms right_half_blocked
#print axioms central_stage_height
#print axioms later_cut_not_faster
#print axioms far_side_arc_inside
#print axioms horizontal_extent
#print axioms centered_crossing_blocked
#print axioms reflected_crossing_blocked
end SwarmRadioLens
