import Lean.Elab.Tactic.Omega
namespace HeadingEvidence
theorem single_step (vS vW bS bW u : Nat) (hv : vS ≤ vW) (hb : bW ≤ bS) :
    max u (vS-bS) ≤ max u (vW-bW) := by omega
theorem heading_order (l0 l1 r0 r1 : Nat) (hl : l1 ≤ l0) (hr : r0 ≤ r1) :
    r0+l1 ≤ r1+l0 := by omega
theorem equal_heading (l0 l1 r0 r1 : Nat) (hl : l1 ≤ l0) (hr : r0 ≤ r1)
    (he : r0+l1 = r1+l0) : l0=l1 ∧ r0=r1 := by omega
theorem late_heading (p q c d : Nat)
    (same : p=q) (bound : d≤1)
    (turn : q+2*d=p+2*c+4) : False := by omega
end HeadingEvidence
