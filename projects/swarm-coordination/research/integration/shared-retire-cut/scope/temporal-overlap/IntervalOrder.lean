import Mathlib
namespace IntervalOrder

theorem active_cycle_cut (t bound : ℤ) :
    t + bound - (t+1) < 0 ↔ bound ≤ 0 := by omega

theorem positive_hold_forced_order
    (e₂ e₃ x₁ x₂ : ℤ)
    (h₁ : x₁ ≤ e₂) (h₂ : x₂ ≤ e₃) (hΔ : e₂+1 ≤ x₂) :
    x₁+1 ≤ e₃ := by omega

theorem forced_order_excludes_overlap
    (t e₂ x₁ : ℤ)
    (h : x₁ ≤ e₂) (he : e₂ ≤ t) (hf : t < x₁) : False := by omega

#print axioms active_cycle_cut
#print axioms positive_hold_forced_order
#print axioms forced_order_excludes_overlap
end IntervalOrder
