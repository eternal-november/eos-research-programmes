import Mathlib

namespace StationReadCut
structure Cut where
  owner : Nat × Bool
  permit : Option Nat
  receipt : Option Nat
  log : List Nat

inductive View where
| refused
| cached (r : Nat)
| pending (l : List Nat)
deriving DecidableEq

def qualified (era payload : Nat) (s : Cut) : Prop :=
  s.owner = (era, true) ∧ s.permit = some payload

instance (era payload : Nat) (s : Cut) : Decidable (qualified era payload s) :=
  inferInstanceAs (Decidable (s.owner = (era, true) ∧ s.permit = some payload))

def view (era payload : Nat) (s : Cut) : View :=
  if qualified era payload s then
    match s.receipt with
    | some r => View.cached r
    | none => View.pending s.log
  else View.refused

theorem refused_ignores_result_and_log (era payload : Nat) (s t : Cut)
    (ha : s.owner = t.owner) (hp : s.permit = t.permit)
    (hq : ¬ qualified era payload s) : view era payload s = view era payload t := by
  have ht : ¬ qualified era payload t := by
    simpa [qualified, ← ha, ← hp] using hq
  simp [view, hq, ht]

theorem cached_ignores_log (era payload r : Nat) (s t : Cut)
    (ha : s.owner = t.owner) (hp : s.permit = t.permit)
    (hq : qualified era payload s) (hr : s.receipt = some r)
    (ht : t.receipt = some r) : view era payload s = view era payload t := by
  have hqt : qualified era payload t := by
    simpa [qualified, ← ha, ← hp] using hq
  simp [view, hq, hqt, hr, ht]

theorem pending_log_exact (era payload : Nat) (s t : Cut)
    (hq : qualified era payload s) (ht : qualified era payload t)
    (hr : s.receipt = none) (hs : t.receipt = none) :
    view era payload s = view era payload t ↔ s.log = t.log := by
  simp [view, hq, ht, hr, hs]

theorem receipt_birth_changes_mode (era payload r : Nat) (s : Cut)
    (hq : qualified era payload s) (hr : s.receipt = none) :
    view era payload s ≠ view era payload { s with receipt := some r } := by
  have ht : qualified era payload { s with receipt := some r } := hq
  simp [view, hq, ht, hr]

#print axioms refused_ignores_result_and_log
#print axioms cached_ignores_log
#print axioms pending_log_exact
#print axioms receipt_birth_changes_mode
end StationReadCut
