import Mathlib

namespace ReceiptPin

theorem allowed_silence_iff (s a b r : Nat) :
    (s < r → a ≤ s ∧ s ≤ b) ↔
      ¬ (s < min a r) ∧ ¬ (b < s ∧ s < r) := by
  omega

theorem common_window (r lo hi : Nat) :
    (∃ t : Nat, r ≤ t ∧ lo ≤ t ∧ t ≤ hi) ↔ max r lo ≤ hi := by
  constructor
  · rintro ⟨t, hr, hl, hh⟩
    omega
  · intro h
    exact ⟨max r lo, by omega, by omega, h⟩

theorem normal_form {W Y : Type} (a b r : W → Nat) (payload : W → Y) (s : Nat) :
  (∃ p : Nat → Y → Nat,
    (∀ w, s < r w → a w ≤ s ∧ s ≤ b w) ∧
    (∀ w, r w ≤ s → r w ≤ p (r w) (payload w) ∧
         a w ≤ p (r w) (payload w) ∧ p (r w) (payload w) ≤ b w)) ↔
  (∀ w, s < r w → a w ≤ s ∧ s ≤ b w) ∧
  (∀ q y, q ≤ s → ∃ t,
    q ≤ t ∧ ∀ w, r w = q → payload w = y → a w ≤ t ∧ t ≤ b w) := by
  classical
  constructor
  · rintro ⟨p, hs, hp⟩
    refine ⟨hs, ?_⟩
    intro q y hq
    refine ⟨max q (p q y), by omega, ?_⟩
    intro w hw hy
    have h := hp w (by omega)
    rw [hw,hy] at h
    omega
  · rintro ⟨hs,hg⟩
    refine ⟨fun q y => (if h : q ≤ s then Classical.choose (hg q y h) else q), hs, ?_⟩
    intro w hw
    simp only [dite_eq_left hw]
    have hp := Classical.choose_spec (hg (r w) (payload w) hw)
    exact ⟨hp.1, hp.2 w rfl rfl⟩

theorem binary_cannot_mark_cycle
    (f : Fin 5 → Fin 2)
    (h02 : f 0 ≠ f 2) (h24 : f 2 ≠ f 4)
    (h41 : f 4 ≠ f 1) (h13 : f 1 ≠ f 3) (h30 : f 3 ≠ f 0) : False := by
  have h (i j : Fin 2) (hn : i ≠ j) :
      i.val + j.val = 1 := by
    have hn' : i.val ≠ j.val := fun he => hn (Fin.ext he)
    omega
  have a := h (f 0) (f 2) h02
  have b := h (f 2) (f 4) h24
  have c := h (f 4) (f 1) h41
  have d := h (f 1) (f 3) h13
  have e := h (f 3) (f 0) h30
  omega

end ReceiptPin
#print axioms ReceiptPin.allowed_silence_iff
#print axioms ReceiptPin.common_window
#print axioms ReceiptPin.normal_form
#print axioms ReceiptPin.binary_cannot_mark_cycle
