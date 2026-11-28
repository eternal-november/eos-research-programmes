import Mathlib
namespace ScopedDoor
structure Pending where
  gate : Nat
  epoch : Nat
  deriving DecidableEq

def valid (epochAt : Nat → Nat) (gate now expiry : Nat) (r : Pending) : Prop :=
  r.gate = gate ∧ r.epoch = epochAt gate ∧ expiry ≤ now

theorem unrelated_edit (f g : Nat → Nat) (gate t e : Nat)
    (r : Pending) (h : f gate = g gate) :
    valid f gate t e r ↔ valid g gate t e r := by
  simp only [valid, h]

theorem stale_after_cut {f : Nat → Nat} {gate t e : Nat} {r : Pending}
    (h : r.epoch ≠ f gate) : ¬ valid f gate t e r :=
  fun hv => h hv.2.1

theorem fit_after_hold_and_before_deadline (ready expiry deadline duration : Nat) :
    (∃ t : Nat, ready ≤ t ∧ expiry ≤ t ∧ t + duration ≤ deadline) ↔
    max ready expiry + duration ≤ deadline := by
  constructor
  · rintro ⟨t, hr, he, hd⟩
    have hm := max_le hr he
    omega
  · intro h
    exact ⟨max ready expiry, le_max_left _ _, le_max_right _ _, h⟩

theorem ingress_check_is_not_effect_check :
    ∃ (f g : Nat → Nat) (r : Pending), valid f 0 0 0 r ∧ ¬ valid g 0 1 0 r := by
  refine ⟨(fun _ => 0), (fun _ => 1), ⟨0,0⟩, ?_⟩
  simp [valid]

theorem no_tokenless_rule (old fresh : Pending) (epoch : Nat)
    (he : old.epoch ≠ epoch) (hf : fresh.epoch = epoch)
    (hg : old.gate = fresh.gate) :
    ¬ (∃ choose : Nat → Bool,
      (choose old.gate = true ↔ old.epoch = epoch) ∧
      (choose fresh.gate = true ↔ fresh.epoch = epoch)) := by
  rintro ⟨c, a, b⟩
  exact he (a.mp (hg ▸ b.mpr hf))

theorem reducer_summary (f : Nat → Nat) (gate : Nat)
    (a b : Pending) (h : (a.gate = gate ∧ a.epoch = f gate) ↔
      (b.gate = gate ∧ b.epoch = f gate)) (t e : Nat) :
    valid f gate t e a ↔ valid f gate t e b := by
  simp only [valid, ← and_assoc]
  exact and_congr h Iff.rfl
end ScopedDoor
