import Mathlib
namespace NativeRecipientCut
def fits (side dock : Bool) (cap : Nat) : Prop :=
  1 + 4 + (if side = dock then 4 else 0) ≤ cap

theorem tight (s d : Bool) {c : Nat} (lo : 5 ≤ c) (hi : c < 9) :
    fits s d c ↔ d ≠ s := by
  cases s <;> cases d <;> simp [fits] <;> omega

theorem twoCopies (copy0 copy1 : Prop) :
    (∀ s : Bool, ∃ d, fits s d 5 ∧ (if d then copy1 else copy0)) ↔
      copy0 ∧ copy1 := by
  constructor
  · intro h
    obtain ⟨a,ha,hA⟩ := h true
    obtain ⟨b,hb,hB⟩ := h false
    cases a <;> cases b <;> simp_all [fits]
  · rintro ⟨a,b⟩ s
    cases s
    · exact ⟨true, by simp [fits], b⟩
    · exact ⟨false, by simp [fits], a⟩

theorem noBlindDock :
    ¬ ∃ d, ∀ s, fits s d 5 := by
  rintro ⟨d,h⟩
  have h' := h d
  simp [fits] at h'

theorem reusableAtNine (s d : Bool) : fits s d 9 := by
  cases s <;> cases d <;> simp [fits]
theorem hintAndReturn (hintBytes cap : Nat) :
    hintBytes + 5 ≤ cap ↔ 5 + hintBytes ≤ cap := by omega

theorem oneInBandTooMany :
    5 ≤ (5 : Nat) ∧ ¬ (1 + 5 ≤ (5 : Nat)) ∧ 1 + 5 ≤ (6 : Nat) := by decide

end NativeRecipientCut
