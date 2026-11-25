import Mathlib

namespace ContingentFleetAuthority

theorem minimum_reserve_strict
    {ι : Type} (s : Finset ι) (r p : ι → ℤ) (b c : ℤ)
    (reserve : ∀ i ∈ s, r i + 1 ≤ p i)
    (prepare : c + 1 ≤ b - ∑ i ∈ s, p i) :
    (∑ i ∈ s, r i) + c + (s.card : ℤ) + 1 ≤ b := by
  have h := Finset.sum_le_sum reserve
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  linarith

theorem strict_floor_suffices
    {ι : Type} (s : Finset ι) (r : ι → ℤ) (b c : ℤ)
    (floor : (∑ i ∈ s, r i) + c + (s.card : ℤ) + 1 ≤ b) :
    ∃ p : ι → ℤ, (∀ i ∈ s, r i + 1 ≤ p i) ∧ c + 1 ≤ b - ∑ i ∈ s, p i := by
  refine ⟨fun i => r i + 1, fun _ _ => le_rfl, ?_⟩
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

theorem a_strictly_accepted_price_can_be_raised_when_two_credits_remain
    (b prev p : ℤ) (spare : 2 ≤ b-prev-p) :
    p < p+1 ∧ 0 < b-prev-(p+1) := by omega

#print axioms minimum_reserve_strict
#print axioms strict_floor_suffices
#print axioms a_strictly_accepted_price_can_be_raised_when_two_credits_remain

end ContingentFleetAuthority
