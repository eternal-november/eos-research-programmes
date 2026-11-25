import Mathlib
namespace BrakeEvidence

noncomputable def advance (t z : ℝ) : ℝ := (t*t+2*t*z-z*z)/4

theorem lateUpper (r z x : ℝ)
    (safe : x + z*z/2 ≤ 1) :
    x + advance r z ≤ 1 + r*r/3 := by
  unfold advance
  nlinarith only [safe,sq_nonneg (3*z-r)]

theorem lateAttained (t : ℝ) (ht : 1 ≤ t) (hlt : t ≤ 4) :
    let r := 4-t
    let z := r/3
    let x := 1-z*z/2
    0 ≤ z ∧ z ≤ t ∧ z ≤ r ∧ z*z/2 ≤ x ∧ x ≤ advance t z ∧
      x+z*z/2 ≤ 1 ∧ x+advance r z = 1+r*r/3 := by
  dsimp [advance]
  have hz0 : 0 ≤ (4-t)/3 := by linarith
  have hz1 : (4-t)/3 ≤ 1 := by linarith
  have hm := mul_nonneg hz0 (sub_nonneg.mpr hz1)
  have hs := mul_nonneg (by linarith [ht] : 0 ≤ t + (4-t)/3-2)
    (by linarith [ht] : 0 ≤ t+(4-t)/3+2)
  constructor
  · exact hz0
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith only [hz1,hm]
  constructor
  · nlinarith only [hs]
  constructor
  · ring_nf; rfl
  · ring

theorem serviceCut (t : ℝ) (h : t ≤ 4) :
    3 ≤ 1+(4-t)*(4-t)/3 ↔ t ≤ 4-Real.sqrt 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hs0 := Real.sqrt_nonneg (6:ℝ)
  have hr : 0 ≤ 4-t := by linarith
  constructor
  · intro hc
    by_contra hn
    have hp : 0 < Real.sqrt 6-(4-t) := by linarith
    have hq : 0 < Real.sqrt 6+(4-t) := by linarith
    nlinarith only [mul_pos hp hq,hs,hc]
  · intro hc
    have hp : 0 ≤ 4-t-Real.sqrt 6 := by linarith
    have hq : 0 ≤ 4-t+Real.sqrt 6 := by linarith
    nlinarith only [mul_nonneg hp hq,hs]

theorem brakingRequired (T b v : ℝ)
    (endpoint_slope : -b*(T-0) ≤ 0-v) : v ≤ b*T := by linarith

#print axioms lateUpper
#print axioms lateAttained
#print axioms serviceCut
#print axioms brakingRequired
end BrakeEvidence
