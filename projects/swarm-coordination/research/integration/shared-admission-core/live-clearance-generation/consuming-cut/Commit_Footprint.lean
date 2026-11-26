import Mathlib

namespace SwarmCommit

inductive Route where
  | p | q
  deriving DecidableEq

structure Cut where
  clear : Bool
  permit : Bool
  backup : Bool
  txP : Nat
  txQ : Nat
  rxBase : Nat
  unrelated : Nat
  deriving DecidableEq

def sender (s : Cut) : Route → Nat
  | .p => s.txP
  | .q => s.txQ

def enabled (s : Cut) : Route → Bool
  | .p => true
  | .q => s.backup

def footprint (s : Cut) (r : Route) : Bool × Bool × Bool × Nat × Nat :=
  (s.clear, s.permit, enabled s r, sender s r, s.rxBase)

def approved (cap bytes : Nat) (v : Bool × Bool × Bool × Nat × Nat) : Prop :=
  v.1 = true ∧ v.2.1 = true ∧ v.2.2.1 = true ∧
  v.2.2.2.1 + bytes ≤ cap ∧ v.2.2.2.2 + bytes ≤ cap

def Admit (cap bytes : Nat) (s : Cut) (r : Route) : Prop :=
  approved cap bytes (footprint s r)

theorem proof_transports_on_effect_footprint {cap bytes : Nat} {observed effect : Cut}
    {r : Route} (h : footprint observed r = footprint effect r) :
    Admit cap bytes observed r ↔ Admit cap bytes effect r := by
  unfold Admit
  rw [h]

instance (cap bytes : Nat) (v : Bool × Bool × Bool × Nat × Nat) : Decidable (approved cap bytes v) := by
  unfold approved
  infer_instance

instance (cap bytes : Nat) (s : Cut) (r : Route) : Decidable (Admit cap bytes s r) :=
  inferInstanceAs (Decidable (approved cap bytes (footprint s r)))

def ready : Cut := ⟨true,true,true,0,0,0,0⟩
def returned : Cut := { ready with clear := false }
def rivalTx : Cut := { ready with txP := 3 }
def rivalRx : Cut := { ready with rxBase := 3 }
def unrelatedWrite : Cut := { ready with unrelated := 1 }

theorem double_sample_is_not_consuming_sample :
    Admit 5 3 ready .p ∧ ¬ Admit 5 3 returned .p := by decide

theorem tx_repair_differs_from_rx_repair :
    ¬ Admit 5 3 rivalTx .p ∧ Admit 5 3 rivalTx .q ∧
    ¬ Admit 5 3 rivalRx .p ∧ ¬ Admit 5 3 rivalRx .q := by decide

theorem unrelated_write_does_not_invalidate :
    unrelatedWrite ≠ ready ∧ footprint ready .p = footprint unrelatedWrite .p ∧
    Admit 5 3 unrelatedWrite .p := by decide

#print axioms proof_transports_on_effect_footprint
#print axioms double_sample_is_not_consuming_sample
#print axioms tx_repair_differs_from_rx_repair
#print axioms unrelated_write_does_not_invalidate
end SwarmCommit
