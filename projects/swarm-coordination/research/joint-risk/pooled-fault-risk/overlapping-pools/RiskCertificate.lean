import Mathlib
open scoped BigOperators
namespace RiskCertificate
theorem cell_upper (x bound rate slack offset : ℚ)
    (h0 : 0 ≤ x) (h1 : x ≤ bound) (hs : 0 ≤ slack)
    (h : rate ≤ slack + offset) :
    x * rate ≤ bound * slack + x * offset := by
  calc
    x * rate ≤ x * (slack + offset) := mul_le_mul_of_nonneg_left h h0
    _ = x * slack + x * offset := by ring
    _ ≤ bound * slack + x * offset :=
      by
        have hbs : x * slack ≤ bound * slack := mul_le_mul_of_nonneg_right h1 hs
        linarith only [hbs]

theorem pooled_upper {I : Type} [Fintype I]
    (x box rate slack offset : I → ℚ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ box i)
    (hs : ∀ i, 0 ≤ slack i) (h : ∀ i, rate i ≤ slack i + offset i)
    (pooled alpha : ℚ)
    (hp : (∑ i, x i * offset i) = pooled)
    (cap : (∑ i, box i * slack i) + pooled ≤ alpha) :
    (∑ i, x i * rate i) ≤ alpha := by
  have hsum := Finset.sum_le_sum
    (s := Finset.univ)
    (fun i _ => cell_upper (x i) (box i) (rate i) (slack i) (offset i)
      (h0 i) (h1 i) (hs i) (h i))
  rw [Finset.sum_add_distrib, hp] at hsum
  exact hsum.trans cap
#print axioms cell_upper
#print axioms pooled_upper
end RiskCertificate
