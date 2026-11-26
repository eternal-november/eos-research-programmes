import Lean

namespace WithdrawalLineage

def step (bay reverse : Bool) : Bool := if reverse then !bay else bay

theorem step_equivariant (bay reverse : Bool) :
    step (!bay) reverse = !(step bay reverse) := by
  cases reverse <;> cases bay <;> rfl

theorem tail_equivariant (tail : List Bool) (bay : Bool) :
    tail.foldl step (!bay) = !(tail.foldl step bay) := by
  induction tail generalizing bay with
  | nil => rfl
  | cons reverse next ih =>
    change next.foldl step (step (!bay) reverse) = !(next.foldl step (step bay reverse))
    rw [step_equivariant]
    exact ih (step bay reverse)

theorem one_gap (after : List Bool) (before : Bool) :
    ((true :: after).foldl step before) ≠ ((false :: after).foldl step before) := by
  change after.foldl step (!before) ≠ after.foldl step before
  rw [tail_equivariant]
  cases after.foldl step before <;> decide

theorem two_exchanges (bay : Bool) :
    [true,true].foldl step bay = bay := by cases bay <;> rfl

#print axioms tail_equivariant
#print axioms one_gap
#print axioms two_exchanges

end WithdrawalLineage
