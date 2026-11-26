import Mathlib
namespace ParityBudget

theorem balanced_joint_exposure (C j : ℕ) (hj : j ≤ C) :
    (C+1)/2 ≤ max j (C-j) := by
  have h1 := le_max_left j (C-j)
  have h2 := le_max_right j (C-j)
  omega

theorem balance_attained (C : ℕ) :
    max (C/2) (C-C/2) = (C+1)/2 := by
  rw [max_eq_right]
  · omega
  · omega

theorem three_resource_comparison :
    (1:ℚ)/4 + ((2:ℚ)/4)*(1/2) = 1/2 ∧
    (1:ℚ)/4 + (2:ℚ)/4 = 3/4 := by norm_num

#print axioms balanced_joint_exposure
#print axioms balance_attained
#print axioms three_resource_comparison
end ParityBudget
