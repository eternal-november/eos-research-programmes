import Lean.Elab.Tactic.Omega
namespace ScopedDisclosure
def Report (cap : Nat) (shared sent : Bool) : Prop :=
  4 + (if shared && sent then 1 else 0) ≤ cap
theorem cap_four_live (sent : Bool) : Report 4 true sent ↔ sent = false := by
  cases sent <;> simp [Report]
theorem no_joint_at_four (sent : Bool) (grant : sent = true) :
    ¬ Report 4 true sent := by simp [grant, Report]
theorem either_meter_insufficient (tx rx : Bool) (h : (tx || rx) = true) :
    ¬ Report 4 (tx || rx) true := by rw [h]; simp [Report]
theorem cap_five (shared sent : Bool) : Report 5 shared sent := by
  cases shared <;> cases sent <;> simp [Report]
theorem mixture (g s idle total : Nat) (h : g + s + idle = total) :
    g + s ≤ total := by omega
end ScopedDisclosure
