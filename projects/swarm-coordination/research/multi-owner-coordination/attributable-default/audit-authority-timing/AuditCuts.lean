import Mathlib

theorem one_slot_cannot_strictly_deter_both (a b : ℚ)
    (h : a + b ≤ 1) : ¬ ((3 : ℚ)/5 < a ∧ (3 : ℚ)/5 < b) := by
  intro ⟨ha, hb⟩
  linarith

theorem early_three_role_audit_obstruction (a b c : ℚ)
    (h : a+b+c ≤ 1) :
    ¬ ((49 : ℚ)/100 < a ∧ (49 : ℚ)/100 < b ∧ (49 : ℚ)/100 < c) := by
  intro ⟨ha,hb,hc⟩
  linarith

theorem late_two_schedules_strictly_deter :
    (49 : ℚ)/100 < 1/2 := by norm_num

#print axioms one_slot_cannot_strictly_deter_both
#print axioms early_three_role_audit_obstruction
#print axioms late_two_schedules_strictly_deter
