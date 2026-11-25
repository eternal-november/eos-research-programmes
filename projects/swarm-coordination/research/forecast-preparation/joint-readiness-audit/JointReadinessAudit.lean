import Mathlib

namespace JointReadinessAudit

theorem audit_below_no_read_line (l h k zl zh : ℝ) (hl : 0 < l) (hh : 0 < h) :
    (k+l*zl)/l + (k+h*(1-zh))/h < 1 ↔
      k*(l+h) < l*h*(zh-zl) := by
  have hp : 0 < l*h := mul_pos hl hh
  have he : ((k+l*zl)/l+(k+h*(1-zh))/h)*(l*h) =
      k*(l+h)+l*h*(1+zl-zh) := by
    field_simp
    ring
  constructor
  · intro x
    have hx := (mul_lt_mul_of_pos_right x hp)
    rw [he] at hx
    nlinarith
  · intro x
    by_contra! hbad
    have hx := mul_le_mul_of_nonneg_right hbad hp.le
    rw [he] at hx
    nlinarith

theorem both_endpoint_changes_are_equal (l h zl zh k a : ℝ)
    (ha : a*(l+h)=l*zl+h*zh) :
    (k+l*(zl-a))-(k-h*(zh-a)) = 0 := by nlinarith

theorem alternating_table_unique
    (d e : List Bool → ℝ)
    (hd : ∀ pre post, d (pre ++ false :: post) = -d (pre ++ true :: post))
    (he : ∀ pre post, e (pre ++ false :: post) = -e (pre ++ true :: post))
    (base : ∀ n, d (List.replicate n true) = e (List.replicate n true)) :
    ∀ xs, d xs = e xs := by
  have aux : ∀ (xs : List Bool) (n : ℕ),
      d (List.replicate n true ++ xs) = e (List.replicate n true ++ xs) := by
    intro xs
    induction xs with
    | nil =>
      intro n
      simpa using base n
    | cons b xs ih =>
      intro n
      have h : List.replicate (n+1) true ++ xs =
          List.replicate n true ++ true :: xs := by
        rw [List.replicate_succ']
        simp
      have ht := ih (n+1)
      rw [h] at ht
      cases b with
      | true => exact ht
      | false =>
        rw [hd, he, ht]
  intro xs
  simpa using aux xs 0

#print axioms alternating_table_unique
#print axioms audit_below_no_read_line
#print axioms both_endpoint_changes_are_equal

end JointReadinessAudit
