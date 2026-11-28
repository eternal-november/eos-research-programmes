import Lean.Elab.Tactic.Omega

namespace Aperture
theorem independent_choices (L R : Nat → Bool → Nat) (cap : Nat → Nat) :
    (∀ t l r, L t l + R t r ≤ cap t) ↔
    (∀ t, max (L t false) (L t true) + max (R t false) (R t true) ≤ cap t) := by
  constructor
  · intro h t
    have h00 := h t false false
    have h01 := h t false true
    have h10 := h t true false
    have h11 := h t true true
    omega
  · intro h t l r
    have hcut := h t
    cases l <;> cases r <;> omega

theorem replacement (old fresh cap : Nat → Nat)
    (admitted : ∀ t, old t ≤ cap t)
    (same_cut : ∀ t, fresh t ≤ old t) :
    ∀ t, fresh t ≤ cap t :=
  fun t => Nat.le_trans (same_cut t) (admitted t)

theorem separate_peaks_sound (L R : Nat → Nat) (lp rp cap : Nat)
    (hl : ∀ t, L t ≤ lp) (hr : ∀ t, R t ≤ rp) (h : lp + rp ≤ cap) :
    ∀ t, L t + R t ≤ cap := by
  intro t
  exact Nat.le_trans (Nat.add_le_add (hl t) (hr t)) h
end Aperture
