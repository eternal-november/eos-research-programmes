import Mathlib
namespace DispatchCut

inductive Arm where
  | plain | early | inline | backup
  deriving DecidableEq

def forcePresent (prior writer : Bool) : Arm → Bool
  | .plain | .backup => prior || writer
  | .early => writer
  | .inline => false

def permit (reserve gate : Bool) : Arm → Bool
  | .plain => true
  | .early | .inline => gate
  | .backup => reserve

def oldPaid (prior writer : Bool) (a : Arm) : Bool :=
  prior || (writer && forcePresent prior writer a)

def newPaid (prior writer reserve : Bool) : Arm → Bool
  | .backup => reserve
  | a => !(forcePresent prior writer a)

def works (prior writer reserve gate : Bool) (a : Arm) : Bool :=
  permit reserve gate a && oldPaid prior writer a && newPaid prior writer reserve a

theorem exact (prior writer reserve gate : Bool) (a : Arm) :
    works prior writer reserve gate a =
      (match a with
        | .plain => false
        | .early => prior && !writer && gate
        | .inline => prior && gate
        | .backup => reserve && (prior || writer)) := by
  cases prior <;> cases writer <;> cases reserve <;> cases gate <;> cases a <;> decide

-- Across the two histories with a live writer but hidden prior dispatch,
-- exactly the preauthorized reserve is a common action.
theorem common (reserve gate : Bool) (a : Arm) :
    (works false true reserve gate a && works true true reserve gate a) =
      (reserve && decide (a = .backup)) := by
  cases reserve <;> cases gate <;> cases a <;> decide

-- The same branch at the same late cut only pays the new duty when old
-- has not paid; calling it a continuation would lose the old one.
theorem cannot_take_old (reserve : Bool) :
    newPaid false true reserve .inline = true ∧
    oldPaid false true .inline = false := by cases reserve <;> decide

end DispatchCut
#print axioms DispatchCut.exact
#print axioms DispatchCut.common
