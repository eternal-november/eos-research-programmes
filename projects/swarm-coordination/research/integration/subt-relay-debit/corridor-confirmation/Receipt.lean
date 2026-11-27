import Mathlib

namespace I2Receipt
inductive View | confirmed | silence deriving DecidableEq
inductive Mode | stop | carry | resend deriving DecidableEq
def view (settled erased : Bool) : View :=
  if settled && !erased then .confirmed else .silence

-- Whether a second physical deposit is authorized at all.
def lawful (idem old : Bool) (m : Mode) : Prop :=
  m = .stop ∨ old = false ∨ idem = true
def delivered (old reached : Bool) (m : Mode) : Prop :=
  old = true ∨ (reached = true ∧ m ≠ .stop)

-- Same timeout both when the attempt failed and when the receipt alone failed.
theorem common_silence : view false false = view true true := by decide

-- No non-idempotent policy can meet exactly-once safety and guaranteed
-- service when both alternatives remain live and the only same-copy choices
-- are first-attempt-stop, carry, or resend.
theorem silent_key_necessary (p : View → Mode)
    (hSafe : lawful false true (p (view true true)))
    (hLive : delivered false true (p (view false false))) : False := by
  rw [common_silence] at hLive
  simp [lawful] at hSafe
  simp [delivered, hSafe] at hLive

theorem named_retry_works (old : Bool) :
    lawful true old .carry ∧ delivered old true .carry := by
  simp [lawful, delivered]

-- An ordered rolling-window boundary on quarter ticks. Strict eviction,
-- not its weak relaxation; canonical representative shifts integer origin.
theorem exact_gate_cut (req check : ℤ) :
    req < check - 4 ↔ req + 5 ≤ check := by omega

theorem gate_adjacent :
    ((-1 : ℤ) < 4 - 4) ∧ ¬((0 : ℤ) < 4 - 4) ∧ ((0 : ℤ) < 5 - 4) := by norm_num

#print axioms common_silence
#print axioms silent_key_necessary
#print axioms named_retry_works
#print axioms exact_gate_cut
#print axioms gate_adjacent
end I2Receipt
