import Mathlib
namespace InFlightHandoff

theorem early_binding_obstruction {View Actor : Type}
    (bind : View → Actor) {left right : View} {a b : Actor}
    (shared : left = right) (switched : a ≠ b) :
    ¬ (bind left = a ∧ bind right = b) := by
  rintro ⟨ha,hb⟩
  exact switched (ha.symm.trans ((congrArg bind shared).trans hb))

def choose (permit : Bool) (actor : Option Nat) : Option Nat :=
  if permit then actor else none

theorem proper_late_successor {x actor : Nat} {permit : Bool}
    (h : choose permit (some actor) = some x) : permit = true ∧ actor = x := by
  cases permit <;> simp [choose] at h ⊢
  exact h

theorem no_local_authority_no_action (permit : Bool) :
    choose permit none = none := by cases permit <;> rfl

end InFlightHandoff
