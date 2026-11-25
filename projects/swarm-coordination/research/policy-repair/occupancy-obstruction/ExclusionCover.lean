import Mathlib

namespace ExclusionCover

theorem overlap_iff (s t h d : ℤ) (hh : 0 < h) (hd : 0 < d) :
    (∃ u : ℤ, s ≤ u ∧ u < s+h ∧ t ≤ u ∧ u < t+d) ↔
        s-d+1 ≤ t ∧ t ≤ s+h-1 := by
  constructor
  · rintro ⟨u,hs,hu,ht,hv⟩
    omega
  · intro ht
    refine ⟨max s t, le_max_left _ _, ?_, le_max_right _ _, ?_⟩ <;> omega

theorem private_slot_gap (prev next t w : ℤ)
    (h1 : prev + w ≤ t) (h2 : t < next) : prev + (w+1) ≤ next := by
  omega

theorem spread (s : ℕ → ℤ) (w : ℤ)
    (gap : ∀ i, s i + (w+1) ≤ s (i+2)) (i m : ℕ) :
      s i + (m:ℤ)*(w+1) ≤ s (i+2*m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := gap (i+2*m)
    have hi : i+2*(m+1)=i+2*m+2 := by omega
    rw [hi]
    push_cast
    linarith only [ih,h]

#print axioms overlap_iff
#print axioms private_slot_gap
#print axioms spread
end ExclusionCover
