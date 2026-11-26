import Mathlib

/-- Two nonempty data chunks; per-chunk metadata is charged separately. -/
theorem two_chunk_cut (l r b h : ℕ) :
    (∃ x : ℕ, 0 < x ∧ x < b ∧ x+h ≤ l ∧ (b-x)+h ≤ r) ↔
      2 ≤ b ∧ h < l ∧ h < r ∧ b+2*h ≤ l+r := by
  constructor
  · rintro ⟨x, px, xb, xl, xr⟩
    omega
  · rintro ⟨hb, hl, hr, hc⟩
    let x := min (l-h) (b-1)
    have xa : 0 < x := by
      dsimp [x]
      omega
    refine ⟨x, xa, ?_, ?_, ?_⟩
    all_goals
      dsimp [x]
      omega

/-- Exact choice threshold after the first charge, without rounding the cut. -/
theorem at_exact_boundary_not_expired (t : ℚ) :
    (0 < t - 1) ↔ (1 < t) := by constructor <;> intro h <;> linarith

#print axioms two_chunk_cut
#print axioms at_exact_boundary_not_expired
