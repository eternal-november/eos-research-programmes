import Mathlib
namespace RelayConfirmation
inductive Body | artifact (key : Nat) | scored (key : Nat) (accepted : Bool) deriving DecidableEq
def pendingNaive (_ : Body) : Bool := false
def pendingTyped (key : Nat) (v : Body) : Bool :=
  match v with
  | .artifact _ => true
  | .scored got ok => !(got == key && ok)
theorem typedSplit (k : Nat) :
  pendingTyped k (.artifact k) = true ∧
  pendingTyped k (.scored k false) = true ∧
  pendingTyped k (.scored k true) = false := by simp [pendingTyped]
theorem noStaleClear {old current : Nat} (h : old ≠ current) :
    pendingTyped current (.scored old true) = true := by
  simp [pendingTyped,h]
theorem capacityBoth {used bytes limit : Nat} :
   (used + bytes ≤ limit ∧ used + bytes + bytes ≤ limit) ↔
   used + 2 * bytes ≤ limit := by omega
theorem capacityFirstOnly {used bytes limit : Nat} (_h : used + bytes ≤ limit)
    (h2 : limit < used + 2 * bytes) : ¬ used + bytes + bytes ≤ limit := by omega
#print axioms typedSplit
#print axioms noStaleClear
#print axioms capacityBoth
#print axioms capacityFirstOnly
end RelayConfirmation
