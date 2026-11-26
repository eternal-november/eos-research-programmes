import Mathlib

namespace SwarmKeyedClosure

def exact (wasPaid retry : Bool) : Prop :=
  (if wasPaid then 1 else 0) + (if retry then 1 else 0) = (1 : Nat)

theorem retry_is_complement (wasPaid retry : Bool) :
    exact wasPaid retry ↔ retry = !wasPaid := by
  cases wasPaid <;> cases retry <;> simp [exact]

theorem identical_view_conflict {View : Type} (decideRetry : View → Bool) (v : View) :
    ¬ (exact false (decideRetry v) ∧ exact true (decideRetry v)) := by
  intro h
  have h₁ := (retry_is_complement false _).mp h.1
  have h₂ := (retry_is_complement true _).mp h.2
  simp_all

def writeOnce (paid : Nat → Bool) (key : Nat) : Nat → Bool :=
  fun q => if q = key then true else paid q

theorem same_key_closed (s : Nat → Bool) (key : Nat) :
    writeOnce s key key = true := by simp [writeOnce]

theorem fresh_key_preserved (s : Nat → Bool) {old fresh : Nat} (h : fresh ≠ old) :
    writeOnce s old fresh = s fresh := by simp [writeOnce,h]

#print axioms retry_is_complement
#print axioms identical_view_conflict
#print axioms same_key_closed
#print axioms fresh_key_preserved
end SwarmKeyedClosure
