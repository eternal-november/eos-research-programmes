import Mathlib

namespace PhysicalSetdown
/-- Model of a reversible actuator: raw toggle is not set-down. -/
def toggle (held : Bool) := !held

def setdown (held : Bool) := if held then toggle held else held

theorem rawRetryUndoes : toggle (toggle true) = true := by decide

theorem guardedPhysicalSetdown (held : Bool) : setdown held = false := by
  cases held <;> decide

theorem guardOnlyNewFails : toggle (setdown true) = true := by decide

theorem allAuthorizedGuarded (held : Bool) (attempts : List Bool)
    (offered : true ∈ attempts) :
    attempts.foldl (fun b run => if run then setdown b else b) held = false := by
  induction attempts generalizing held with
  | nil => simp at offered
  | cons x xs ih =>
    cases x
    · have tail : true ∈ xs := by simpa using offered
      exact ih held tail
    · have step : ∀ ys : List Bool,
          ys.foldl (fun b run => if run then setdown b else b) false = false := by
        intro ys
        induction ys with
        | nil => rfl
        | cons y ys iy =>
          rw [List.foldl_cons]
          cases y <;> simpa [setdown] using iy
      rw [List.foldl_cons]
      simpa [guardedPhysicalSetdown] using step xs

end PhysicalSetdown

#print axioms PhysicalSetdown.rawRetryUndoes
#print axioms PhysicalSetdown.guardedPhysicalSetdown
#print axioms PhysicalSetdown.guardOnlyNewFails
#print axioms PhysicalSetdown.allAuthorizedGuarded
