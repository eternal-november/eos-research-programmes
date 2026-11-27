import Mathlib
namespace StaggeredDensity

theorem narrowMean {a b d η : ℝ} (mean : |a|  ≤  η)
    (big : 3/2 - η  ≤  d) (gapLo : 0  ≤  a-b-d) (gapHi : a-b+d  ≤  3) :
    -(3/2)-2*η  ≤  b ∧ b  ≤  -(3/2)+2*η := by
  have h := abs_le.mp mean
  constructor  <;> linarith

theorem symmetricPower {v w u : ℝ} (hv : |v| ≤ u) (hw : |w| ≤ u) :
    |(v+w)/2|  ≤  u-(v-w)/2 := by
  have p := abs_le.mp hv
  have q := abs_le.mp hw
  apply abs_le.mpr
  constructor  <;> linarith

theorem excludesSmallDeficit {η q : ℝ} (hn : 0 ≤ q)
    (vBound : q*q ≤ 16*η) (reach : 3/8 ≤ 2*η+3*q/4) : 1/100 < η := by
  by_contra! low
  have small : q ≤ 2/5 := by nlinarith
  linarith

theorem positiveTemplate {F G : ℝ} (g0 : 0 ≤ G) (ord : G ≤ F) (cap : F ≤ 2) :
    0 ≤ (F-G)/4 ∧ (F+G)/4 ≤ 3 ∧ 0 ≤ 3*F/2 ∧ 3*F/2 ≤ 3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor  <;> linarith
#print axioms narrowMean
#print axioms symmetricPower
#print axioms excludesSmallDeficit
#print axioms positiveTemplate
end StaggeredDensity
