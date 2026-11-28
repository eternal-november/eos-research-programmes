import Mathlib
namespace RetryBinding

inductive Action (R : Type) where
  | execute (actor : Nat)
  | returnResult (value : R)
  | refuse
  deriving DecidableEq

def retry {R : Type} (saved : Option R) (mayDisclose : Bool) (current : Option Nat) :
    Action R :=
  match saved with
  | some r => if mayDisclose then .returnResult r else .refuse
  | none => match current with
    | some a => .execute a
    | none => .refuse

theorem past_binding_is_not_reinterpreted {R : Type} (r : R) (a b : Option Nat) :
    retry (some r) true a = retry (some r) true b := rfl

theorem no_disclosure_not_new_execution {R : Type} (r : R) (current : Option Nat) :
    retry (some r) false current = .refuse := rfl

theorem receipt_even_without_actuator {R : Type} (r : R) :
    retry (some r) true none = .returnResult r := rfl

theorem unsettled_uses_current {R : Type} (b : Bool) (actor : Nat) :
    retry (none : Option R) b (some actor) = .execute actor := rfl

end RetryBinding
