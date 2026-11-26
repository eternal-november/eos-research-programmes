import Mathlib
namespace DirectedBraking

theorem tight_chain_impossible (h p q s₁ s₂ s₃ : ℝ)
    (hh : 0 < h) (hp : 0 < p) (hq : 0 < q)
    (h₁ : (2*h)*s₁ = p^2) (h₂ : (2*h)*s₂ = q^2)
    (h₃ : (p+q)^2 ≤ (2*h)*s₃) (ht : s₃ ≤ s₁+s₂) : False := by
  have hmul := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*h by positivity)
  linarith [mul_pos hp hq, show (2*h)*(s₁+s₂) = (2*h)*s₁+(2*h)*s₂ by ring,
    show (p+q)^2 = p^2+q^2+2*(p*q) by ring]

theorem heterogeneous_span_arithmetic :
    (1:ℚ)/20 = (3-2)^2/(2*(9+1)) ∧
    (1:ℚ) = (2-0)^2/(2*(1+1)) ∧
    ((3:ℚ)-0)^2/(2*(9+1)) < 21/20 := by norm_num

#print axioms tight_chain_impossible
#print axioms heterogeneous_span_arithmetic
end DirectedBraking
