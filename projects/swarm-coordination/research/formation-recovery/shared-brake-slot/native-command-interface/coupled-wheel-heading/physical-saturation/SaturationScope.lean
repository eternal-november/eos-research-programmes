import Lean.Elab.Tactic.Omega
namespace SaturationScope
theorem right_only (left right0 right1 : Nat)
  (minStop : 16 ≤ left) (straight : right0 = left)
  (turned : right1 = left+4) : 32 ≤ left+right0 ∧ 36 ≤ left+right1 := by omega
theorem left_only (right left0 left1 : Nat)
  (minStop : 16 ≤ right) (straight : left0 = right)
  (turned : right = left1+4) : 32 ≤ right+left0 ∧ 28 ≤ right+left1 := by omega
theorem common_effect (left right : Nat) : ¬ (right=left ∧ right=left+4) := by omega
end SaturationScope
