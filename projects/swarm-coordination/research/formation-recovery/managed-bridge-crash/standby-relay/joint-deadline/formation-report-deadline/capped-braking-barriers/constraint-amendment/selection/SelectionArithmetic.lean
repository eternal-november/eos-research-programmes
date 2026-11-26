import Mathlib
namespace FormationSelection

theorem slack_cut_equivalence (l L : ℕ) :
    (1:ℚ)/2 + (l:ℚ)/(2*((L:ℚ)+1)) < 1 ↔ l ≤ L := by
  have h : (0:ℚ) < 2*((L:ℚ)+1) := by positivity
  have key : (1:ℚ)/2 + (l:ℚ)/(2*((L:ℚ)+1)) < 1 ↔ (l:ℚ) < (L:ℚ)+1 := by
    rw [show ((1:ℚ)/2 + (l:ℚ)/(2*((L:ℚ)+1)) < 1) ↔
         (l:ℚ)/(2*((L:ℚ)+1)) < 1/2 by constructor <;> intro hh <;> linarith]
    rw [div_lt_iff₀ h]
    constructor <;> intro hh <;> linarith
  rw [key, ← Nat.cast_succ]
  exact_mod_cast Nat.lt_succ_iff

#print axioms slack_cut_equivalence
end FormationSelection
