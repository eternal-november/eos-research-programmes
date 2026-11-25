import Mathlib
namespace AuditThreshold
theorem wins_when_calibrated (c e : ℚ) (hc : c < 1 / 2) :
    3 / 2 - e / 2 > 1 + c + (3 - 4 * c) * (e / 2) ↔
      e < (1 / 2 - c) / (2 * (1 - c)) := by
  have hd : 0 < 2 * (1 - c) := by linarith
  rw [lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

theorem quarter_threshold (e : ℚ) :
    3 / 2 - e / 2 > 5 / 4 + e ↔ e < 1 / 6 := by
  constructor <;> intro h <;> linarith
#print axioms wins_when_calibrated
#print axioms quarter_threshold
end AuditThreshold
