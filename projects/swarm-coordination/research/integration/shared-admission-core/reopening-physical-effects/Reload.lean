import Mathlib

namespace RepeatedEffect

def guard (held : Bool) (command live : Nat) : Bool :=
  held && decide (command = live)

theorem oldFenceCurrentReuse {old now : Nat} (changed : old ≠ now) :
    guard true old now = false ∧ guard true now now = true := by
  simp [guard,changed]

theorem reusedEpochMatches (e : Nat) :
    guard true e e = true := by simp [guard]

/-- An old load state is restored at the same site by a later operation.
    A rule on the state alone cannot admit the original command and then
    exclude a delayed copy at that same state. -/
theorem sameStateSameControl {S : Type} (permit : S → Bool) (x y : S)
    (same : x = y) (authorized : permit x = true) : permit y = true :=
  same ▸ authorized

def hazardous (arrives pickup leaves : Nat) : Prop :=
  pickup < arrives ∧ arrives < leaves

theorem outerProductAddsCounterhistory :
    ¬ hazardous 3 4 6 ∧ ¬ hazardous 1 2 6 ∧ hazardous 3 2 6 := by
  unfold hazardous
  decide

end RepeatedEffect

#print axioms RepeatedEffect.oldFenceCurrentReuse
#print axioms RepeatedEffect.reusedEpochMatches
#print axioms RepeatedEffect.sameStateSameControl
#print axioms RepeatedEffect.outerProductAddsCounterhistory
