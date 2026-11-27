import Mathlib
open scoped BigOperators
namespace CarriedRisk

def ind (b : Bool) : ℚ := if b then 1 else 0

theorem report_majorizes (x y : Bool) (h : x=true → y=true) :
    ind (x || y) ≤ ind y := by
  cases x <;> cases y <;> simp_all [ind]

theorem expected_bound {Ω : Type} [Fintype Ω]
    (prob score upper : Ω → ℚ) (nonneg : ∀ o, 0 ≤ prob o)
    (check : ∀ o, 0 < prob o → score o ≤ upper o) :
    (∑ o, prob o * score o) ≤ ∑ o, prob o * upper o := by
  apply Finset.sum_le_sum
  intro o _
  by_cases h : 0 < prob o
  · exact mul_le_mul_of_nonneg_left (check o h) (nonneg o)
  · have z : prob o = 0 := by linarith [nonneg o]
    simp [z]

#print axioms report_majorizes
#print axioms expected_bound
end CarriedRisk
