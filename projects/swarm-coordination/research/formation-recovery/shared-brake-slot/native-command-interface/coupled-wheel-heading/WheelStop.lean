import Lean.Elab.Tactic.Omega
namespace WheelStop
theorem late_cut (p q x0 y0 x1 y1 : Nat)
    (hp : 16 ≤ p) (h0 : x0 ≤ 1) (h1 : y1 ≤ 1)
    (straight : q + 2*y0 = p + 2*x0)
    (turned : q + 2*y1 = p + 2*x1 + 4) :
    x0 = 1 ∧ y0 = 0 ∧ x1 = 0 ∧ y1 = 1 ∧ 36 ≤ p+q+2*(x0+y0) := by omega
theorem one_tick_shared (accum l r : Nat) :
    ¬ (accum + r = l ∧ accum + r = l+4) := by omega
theorem axis_does_not_imply_wheel :
    (1 : Nat) ≤ 1 ∧ (1 : Nat) ≤ 1 ∧ ¬ (1+1 : Nat) ≤ 1 := by decide
end WheelStop
