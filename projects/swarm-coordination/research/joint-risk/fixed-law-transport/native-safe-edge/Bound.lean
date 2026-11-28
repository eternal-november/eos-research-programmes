import Lean.Elab.Tactic.Omega
namespace NativeRisk
-- Probabilities are represented in common units; no distribution is estimated.
def feasible (n p q t : Int) : Prop :=
  0 ≤ t ∧ t ≤ p ∧ t ≤ q ∧ 0 ≤ n-p-q+t

theorem enlarged_max (n p q : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hnp : p ≤ n) (hnq : q ≤ n) :
    feasible n p q (min p q) ∧
    (∀ t, feasible n p q t → n-p-q+t ≤ n-max p q) ∧
    n-p-q+min p q = n-max p q := by
  constructor
  · unfold feasible; omega
  · constructor
    · intro t h; unfold feasible at h; omega
    · omega

theorem restricted_max (n p q : Int) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    feasible n p q 0 ↔ p+q ≤ n := by
  unfold feasible
  omega

theorem changed_safe_edge_gap (n p q : Int) :
    (n-max p q) - (n-p-q) = min p q := by omega

theorem restricted_certificate_requires_missing_safe_edge
    (u0 u1 v0 v1 : Int)
    (h00 : 1 ≤ u0+v0) (h11 : 0 ≤ u1+v1) :
    1 ≤ u0+u1+v0+v1 := by omega
end NativeRisk
