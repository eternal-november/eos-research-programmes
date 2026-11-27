import Mathlib
namespace SelectiveDensity

theorem blindNeighbor {p x y span cap : ℝ}
    (xl : span  ≤  x-p) (xu : x-p  ≤  cap) (yl : span  ≤  y-p)
    (yu : y-p  ≤  cap) : |x-y|  ≤  cap-span := by
  apply abs_le.mpr
  constructor <;> linarith

theorem preSpread {p z near far : ℝ}
    (pEnough : z ≤ p) (nearEnough : 2*z ≤ near) (farNonnegative : 0 ≤ far)
    (totalEnough : p+z ≤ near+far) :
    ∃ s : ℝ, z ≤ s ∧ s+z ≤ near ∧ 0 ≤ p-s ∧ p-s ≤ far := by
  refine ⟨max z (p-far), le_max_left _ _, ?_, ?_, ?_⟩
  · have h : max z (p-far) ≤ near-z := max_le (by linarith) (by linarith)
    linarith
  · have h : max z (p-far) ≤ p := max_le pEnough (by linarith)
    linarith
  · have h := le_max_right z (p-far)
    linarith

theorem safeNear {s z p q h : ℝ} (nonneg : 0 ≤ q)
    (ord : q ≤ p) (bnd : p ≤ 1) (hz : 0 ≤ z) (cover : z ≤ s)
    (cap : s+z ≤ h) : 0 ≤ s*p-z*q ∧ s*p+z*q ≤ h := by
  have sNonneg : 0 ≤ s := by linarith
  have hp : 0 ≤ p := by linarith
  have h1 := mul_le_mul_of_nonneg_left ord hz
  have h2 := mul_le_mul_of_nonneg_right cover hp
  have h3 := mul_le_mul_of_nonneg_left bnd (show 0 ≤ s+z by linarith)
  constructor <;> nlinarith

theorem crossMass {a b c d : ℝ}
    (ordered : a*d ≤ b*c) :
    a*(b+d) ≤ b*(a+c) := by nlinarith

#print axioms blindNeighbor
#print axioms preSpread
#print axioms safeNear
#print axioms crossMass
end SelectiveDensity
