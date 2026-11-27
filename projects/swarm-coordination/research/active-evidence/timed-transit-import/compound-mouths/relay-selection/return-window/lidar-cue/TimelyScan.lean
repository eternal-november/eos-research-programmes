import Mathlib

namespace TimelyScan

-- Closure at a scheduled sample is conservatively ordered after it.
def nextStrict (period phase : ℕ) : ℕ := period - phase % period

theorem allPhases (period consume budget : ℕ) :
    (∀ phase, nextStrict period phase + consume ≤ budget)
      ↔ period + consume ≤ budget := by
  constructor
  · intro h
    simpa [nextStrict, Nat.zero_mod] using h 0
  · intro h phase
    apply le_trans (Nat.add_le_add_right (Nat.sub_le _ _) _) h

theorem positiveGap (period phase : ℕ) (hp : 0 < period) :
    0 < nextStrict period phase := by
  unfold nextStrict
  exact Nat.sub_pos_of_lt (Nat.mod_lt _ hp)

#print axioms allPhases
#print axioms positiveGap
end TimelyScan
