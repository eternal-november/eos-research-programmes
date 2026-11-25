import Mathlib

namespace SwarmOffsetMatching

def eligible (s r lo hi x : ℚ) := lo ≤ r - (s + x) ∧ r - (s + x) ≤ hi

theorem interval_form (s r lo hi x : ℚ) :
    eligible s r lo hi x ↔ r-s-hi ≤ x ∧ x ≤ r-s-lo := by
  unfold eligible
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem straight_feasible (x : ℚ) :
    eligible 0 0 0 1 x ∧ eligible 2 2 0 1 x ↔ -1 ≤ x ∧ x ≤ 0 := by
  unfold eligible
  constructor
  · intro ⟨h,_⟩
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro ⟨h,k⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem cross_has_no_common_shift (x : ℚ) :
    ¬ (eligible 0 2 0 1 x ∧ eligible 2 0 0 1 x) := by
  unfold eligible
  intro ⟨h,k⟩
  linarith [h.2,k.1]

theorem cross_marginals_feasible :
    (∃ x : ℚ, -3 ≤ x ∧ x ≤ 3 ∧ eligible 0 2 0 1 x) ∧
    (∃ x : ℚ, -3 ≤ x ∧ x ≤ 3 ∧ eligible 2 0 0 1 x) := by
  exact ⟨⟨1,by norm_num [eligible]⟩,⟨-2,by norm_num [eligible]⟩⟩

theorem dummy_consumption (m k dummy real : ℕ) (h0 : k ≤ m)
    (h1 : dummy = m-k) (h2 : real + dummy = m) : real = k := by
  omega

#print axioms interval_form
#print axioms straight_feasible
#print axioms cross_has_no_common_shift
#print axioms cross_marginals_feasible
#print axioms dummy_consumption
end SwarmOffsetMatching
