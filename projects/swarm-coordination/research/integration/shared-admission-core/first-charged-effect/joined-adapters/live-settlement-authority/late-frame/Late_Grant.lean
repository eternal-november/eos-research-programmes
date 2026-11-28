import Mathlib
namespace QualifiedDelivery

def install (active incoming : Nat) (present : Bool) : Bool :=
  present || decide (incoming = active)

theorem order_independent (active a b : Nat) (present : Bool) :
    install active b (install active a present) =
      install active a (install active b present) := by
  simp [install, Bool.or_left_comm, Bool.or_assoc, Bool.or_comm]

theorem stale_cannot_install {active stale : Nat} (ne : stale ≠ active) :
    install active stale false = false := by
  simp [install,ne]

theorem physical_debit_obstruction {cap : Nat} (h : cap = 5) :
    1+4 ≤ cap ∧ ¬ (1+1+4 ≤ cap) := by omega

end QualifiedDelivery
