import Mathlib

namespace SwarmClockCut

def arrivalA (x la c : ℚ) : Prop := x < 0 ∧ x + la ≤ c
def arrivalB (x lb c : ℚ) : Prop := -1 < x ∧ lb ≤ c

theorem physical_capture (x : ℚ) : x < 0 ∨ -1 < x := by
  by_cases h : x < 0
  · exact Or.inl h
  · right
    linarith [le_of_not_gt h]

theorem exact_receipt_cut (c : ℚ) :
    (∀ x la lb : ℚ, -1 ≤ x → x ≤ 1 → 1 ≤ la → la ≤ 2 →
       1 ≤ lb → lb ≤ 2 → arrivalA x la c ∨ arrivalB x lb c) ↔ 2 ≤ c := by
  constructor
  · intro h
    have hh := h 0 2 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    simpa [arrivalA, arrivalB] using hh
  · intro c2 x la lb h0 h1 la0 la2 lb0 lb2
    rcases physical_capture x with h | h
    · exact Or.inl ⟨h, by linarith⟩
    · exact Or.inr ⟨h, by linarith⟩

theorem no_fixed_route (c : ℚ) :
    (¬ ∀ x : ℚ, -1 ≤ x → x ≤ 1 → arrivalA x 1 c) ∧
    (¬ ∀ x : ℚ, -1 ≤ x → x ≤ 1 → arrivalB x 1 c) := by
  constructor
  · intro h
    have hh := h 1 (by norm_num) (by norm_num)
    norm_num [arrivalA] at hh
  · intro h
    have hh := h (-1) (by norm_num) (by norm_num)
    norm_num [arrivalB] at hh

theorem split_calibration_loses_joint_capture :
    ∃ x y : ℚ, -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧
      ¬ (x < 0 ∨ -1 < y) := by
  refine ⟨0,-1,?_⟩
  norm_num

#print axioms physical_capture
#print axioms exact_receipt_cut
#print axioms no_fixed_route
#print axioms split_calibration_loses_joint_capture
end SwarmClockCut
