import Mathlib
namespace ScopedArchive
inductive Decision | refuse | replay | returnResult (v : Nat) deriving DecidableEq
def consume (qualified : Bool) (result : Option Nat) (fenced permit : Bool) :=
 if !qualified then Decision.refuse else
  match result with
  | some n => Decision.returnResult n
  | none => if fenced && permit then Decision.replay else Decision.refuse
theorem positiveRead (n : Nat) (fenced permit : Bool) :
    consume true (some n) fenced permit = .returnResult n := by simp [consume]
theorem staleRead (r : Option Nat) (fenced permit : Bool) :
    consume false r fenced permit = .refuse := by simp [consume]
theorem negativeNotAuthority (permit : Bool) :
    consume true none false permit = .refuse := by simp [consume]
theorem replayNeedsAll (q f p : Bool) (r : Option Nat)
    (h : consume q r f p = .replay) : q = true ∧ r = none ∧ f = true ∧ p = true := by
  cases q <;> cases r <;> cases f <;> cases p <;> simp [consume] at *
#print axioms positiveRead
#print axioms staleRead
#print axioms negativeNotAuthority
#print axioms replayNeedsAll
end ScopedArchive
