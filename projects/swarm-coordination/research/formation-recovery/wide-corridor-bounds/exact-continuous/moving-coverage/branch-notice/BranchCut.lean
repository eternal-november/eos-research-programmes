import Mathlib
namespace BranchCut

theorem propagation (l u y d : ℝ) (hu : l ≤ u) (hd : 0 ≤ d) :
    (∃ x : ℝ, l ≤ x ∧ x ≤ u ∧ |y - x| ≤ d) ↔
        l - d ≤ y ∧ y ≤ u + d := by
  constructor
  · rintro ⟨x,h1,h2,h3⟩
    rw [abs_le] at h3
    constructor <;> linarith [h3.1,h3.2]
  · rintro ⟨h1,h2⟩
    let x := max l (y-d)
    have hx : x ≤ u := max_le hu (by linarith)
    refine ⟨x,le_max_left _ _,hx,?_⟩
    rw [abs_le]
    have hi : y-d ≤ x := le_max_right _ _
    have hj : x ≤ y+d := max_le (by linarith) (by linarith)
    constructor <;> linarith

noncomputable def cut (h : ℝ) : ℝ :=
  if h ≤ 19/3 then 7-h else (23/3-h)/2

/-- The right hand bound on the common seam comes from a still-owed
    seam overlap plus the remaining retreat time to that overlap. -/
theorem seam_cut (h r : ℝ) :
    (h - 3 + r ≤ 4 + max 0 (2/3-r)) ↔ r ≤ cut h := by
  unfold cut
  by_cases h₁ : h ≤ 19/3
  · rw [if_pos h₁]
    by_cases h₂ : r ≤ 2/3
    · have he : max 0 (2/3-r) = 2/3-r := max_eq_right (by linarith)
      rw [he]
      constructor <;> intro hh <;> linarith
    · rw [max_eq_left (by linarith)]
      constructor <;> intro hh <;> linarith
  · rw [if_neg h₁]
    by_cases h₂ : r ≤ 2/3
    · have he : max 0 (2/3-r) = 2/3-r := max_eq_right (by linarith)
      rw [he]
      constructor <;> intro hh <;> linarith
    · rw [max_eq_left (by linarith)]
      constructor <;> intro hh <;> linarith

theorem high_cut_after_far_seam (h : ℝ) (hp : 0 < h)
    (hh : 19/3 ≤ h) (hf : h + 4/h ≤ 7) : 4/h ≤ (23/3-h)/2 := by
  linarith

#print axioms propagation
#print axioms seam_cut
#print axioms high_cut_after_far_seam
end BranchCut
