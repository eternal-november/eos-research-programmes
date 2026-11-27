import Mathlib
namespace DeadlineLaw

noncomputable def best (t : ℝ) := max (1/2) (max (2*t) (1-2*t))
noncomputable def worst (l u : ℝ) := max (1/2) (max (2*l) (1-2*u))

theorem lower (l u t : ℝ) (h₁ : l≤t) (h₂ : t≤u) : worst l u≤best t := by
  unfold worst best
  apply max_le_max le_rfl
  apply max_le_max <;> linarith

theorem attained (l u : ℝ) (h : l≤u) :
    ∃ t, l≤t ∧ t≤u ∧ best t=worst l u := by
  by_cases h₁ : (1:ℝ)/4≤l
  · refine ⟨l,le_rfl,h,?_⟩
    unfold best worst
    rw [max_eq_left (by linarith : 1-2*l≤2*l)]
    rw [max_eq_left (by linarith : 1-2*u≤2*l)]
  · by_cases h₂ : u≤(1:ℝ)/4
    · refine ⟨u,h,le_rfl,?_⟩
      unfold best worst
      rw [max_eq_right (by linarith : 2*u≤1-2*u)]
      rw [max_eq_right (by linarith : 2*l≤1-2*u)]
    · refine ⟨1/4,by linarith,by linarith,?_⟩
      have h₃ : max (2*l) (1-2*u)≤(1:ℝ)/2 :=
        max_le (by linarith) (by linarith)
      unfold best worst
      rw [max_eq_left h₃]
      norm_num
#print axioms lower
#print axioms attained
end DeadlineLaw
