import Mathlib
open scoped BigOperators
namespace DefaultEvidence

variable {O : Type} [Fintype O] [DecidableEq O]

def maximal (safeSet : Finset O) (b : ℕ) (o : O) : ℕ :=
  if o ∈ safeSet then 0 else b

theorem cap_optimal (safeSet : Finset O) (w : O → ℕ) (b : ℕ)
    (fine : O → ℕ) (cap : ∀ o, fine o ≤ b)
    (innocent : ∀ o ∈ safeSet, fine o = 0) :
    (∑ o, w o * fine o) ≤ ∑ o, w o * maximal safeSet b o := by
  apply Finset.sum_le_sum
  intro o _
  apply Nat.mul_le_mul_left
  by_cases h : o ∈ safeSet
  · simp [maximal, h, innocent o h]
  · simpa [maximal, h] using cap o

theorem exact_cap (safeSet : Finset O) (w : O → ℕ) (b d : ℕ) :
    (∃ fine : O → ℕ, (∀ o, fine o ≤ b) ∧
       (∀ o ∈ safeSet, fine o = 0) ∧ d < ∑ o, w o * fine o) ↔
      d < ∑ o, w o * maximal safeSet b o := by
  constructor
  · rintro ⟨f, hcap, hgood, hp⟩
    exact lt_of_lt_of_le hp (cap_optimal safeSet w b f hcap hgood)
  · intro h
    refine ⟨maximal safeSet b, ?_, ?_, h⟩
    · intro o
      by_cases g : o ∈ safeSet <;> simp [maximal, g]
    · intro o ho
      simp [maximal, ho]

theorem optimal_with_no_signal (safeSet : Finset O) (w : O → ℕ)
    (allWitnessesProtected : ∀ o, o ∉ safeSet → w o = 0) (b : ℕ) :
    (∑ o, w o * maximal safeSet b o) = 0 := by
  apply Finset.sum_eq_zero
  intro o _
  by_cases h : o ∈ safeSet
  · simp [maximal, h]
  · simp [maximal, h, allWitnessesProtected o h]

#print axioms cap_optimal
#print axioms exact_cap
#print axioms optimal_with_no_signal
end DefaultEvidence
