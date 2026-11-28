import Mathlib
namespace JournalWire
inductive Handoff (A : Type) where
  | missing
  | pending
  | settled (record : A)

def admission {A : Type} : Handoff A → Bool → Bool
  | .missing, _ => false
  | .pending, clear => clear
  | .settled _, _ => true

theorem absence_is_not_pending :
    admission (Handoff.missing : Handoff Nat) true = false ∧
    admission (Handoff.pending : Handoff Nat) true = true :=
  ⟨rfl,rfl⟩

theorem both_directions_required (stored incoming load q b : Nat) :
    ((stored + incoming ≤ q) ∧ (load + 4 ≤ b)) ↔
      (stored ≤ q ∧ incoming ≤ q - stored) ∧ (load ≤ b ∧ 4 ≤ b - load) := by
  omega

theorem live_record_bounds (cap : Nat) :
    (1 + 4 ≤ cap ↔ 5 ≤ cap) ∧ (5 + 4 ≤ cap ↔ 9 ≤ cap) := by
  norm_num

theorem settled_needs_no_new_move {A : Type} (a : A) :
    admission (.settled a) false = true := rfl
end JournalWire
