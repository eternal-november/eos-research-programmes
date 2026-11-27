import Mathlib
namespace MovingDensity

theorem mirrorCenter {left right : ℝ} (h : left=right) : (left-right)/2=0 := by linarith

theorem mirrorConvexGap {a b c d g r : ℝ}
    (s1 : g ≤ b-a) (s2 : g ≤ d-c) (u1 : b-a ≤ r) (u2 : d-c ≤ r) :
    g ≤ (b+d)/2 - (a+c)/2 ∧ (b+d)/2 - (a+c)/2 ≤ r := by
  constructor <;> linarith

theorem deadlineNecessary {L M B C δ : ℝ}
    (startBound : -B≤L) (lateBound : M≤C) (demand : δ≤M-L) : δ≤B+C := by linarith

theorem scaledInactive {F G A C k : ℝ} (h0 : 0≤G) (h1 : G≤F)
    (h2 : F≤A) (h3 : 0≤C) (hk : 0≤k) :
    0≤k*(F-G) ∧ k*(F-G)≤k*(A+C) := by
  constructor
  · exact mul_nonneg hk (sub_nonneg.mpr h1)
  · exact mul_le_mul_of_nonneg_left (by linarith) hk

#print axioms mirrorCenter
#print axioms mirrorConvexGap
#print axioms deadlineNecessary
#print axioms scaledInactive
end MovingDensity
