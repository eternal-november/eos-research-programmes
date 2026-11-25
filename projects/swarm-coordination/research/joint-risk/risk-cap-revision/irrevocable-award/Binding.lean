import Mathlib
namespace Binding

theorem timely_bound (e h a r : ℚ)
    (mass : e + h + a = 1) (rate : r ≤ h) (budget : e / 4 + r / 2 ≤ 1 / 8) (hr : 0 ≤ r) :
    7 / 4 * e + 3 / 2 * a + 5 / 4 * h + r / 2 ≤ 13 / 8 := by
  linarith

theorem original_bound (e h a r : ℚ)
    (mass : e + h + a = 1) (rate : r ≤ h) (budget : e / 4 + r / 2 ≤ 1 / 4) (hr : 0 ≤ r) :
    7 / 4 * e + 3 / 2 * a + 5 / 4 * h + r / 2 ≤ 7 / 4 := by
  linarith

theorem old_stays_in_union (old both : ℚ) (already : old = 1 / 4) (stand : old ≤ both) :
    ¬ both ≤ 1 / 8 := by
  intro h
  linarith

theorem forced_hold_bound (r : ℚ) (budget : r / 2 ≤ 1 / 8) :
    5 / 4 + r / 2 ≤ 11 / 8 := by linarith

#print axioms timely_bound
#print axioms original_bound
#print axioms old_stays_in_union
#print axioms forced_hold_bound
end Binding
