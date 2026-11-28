import Mathlib
namespace DockCut

inductive Dock where
  | r | s
  deriving DecidableEq

def current (moved : Bool) : Dock := if moved then .s else .r

def nativeGrant (moved delivered transfer : Bool) : Option Dock :=
  if delivered && (!moved || transfer) then some (current moved) else none

def admitted (moved delivered transfer : Bool) (a b c : ℕ) : Prop :=
  delivered = true ∧ (moved = true → transfer = true) ∧ a+b ≤ c

def paid (moved delivered transfer : Bool) (a b c : ℕ) : Prop :=
  nativeGrant moved delivered transfer = some (current moved) ∧ a+b ≤ c

theorem fresh_exact (moved delivered transfer : Bool) (a b c : ℕ) :
    paid moved delivered transfer a b c ↔ admitted moved delivered transfer a b c := by
  cases moved <;> cases delivered <;> cases transfer <;> simp [paid, admitted, nativeGrant]

theorem only_current (moved delivered transfer : Bool) (d : Dock)
    (h : nativeGrant moved delivered transfer = some d) : d = current moved := by
  cases moved <;> cases delivered <;> cases transfer <;>
    simp_all [nativeGrant, current]

theorem no_uninformed_dock (d : Dock) :
    ¬ (d = current false ∧ d = current true) := by cases d <;> decide

theorem capacity_separation (a b : ℕ) :
    a+b ≤ a+b ∧ ¬ (a+b+1 ≤ a+b) := by omega

theorem shared_window_cut (a b c : ℕ) (aPos : 0 < a) (fit : a+b ≤ c)
    (tight : a+b+1 > c) : ¬ (a+a+b ≤ c) := by omega

end DockCut
#print axioms DockCut.fresh_exact
#print axioms DockCut.no_uninformed_dock
#print axioms DockCut.shared_window_cut
