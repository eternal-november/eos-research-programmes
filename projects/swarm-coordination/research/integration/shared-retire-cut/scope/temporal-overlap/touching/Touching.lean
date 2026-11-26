import Mathlib
namespace Touching

def earlier (x y : ℝ) (endOpen startOpen : Prop) :=
  x < y ∨ (x = y ∧ (endOpen ∨ startOpen))

theorem closure_under_positive_middle
    (xi ej xj ek : ℝ) (iEnd jStart jEnd kStart : Prop)
    (hw : ej ≤ xj) (hs : jStart → jEnd → ej < xj)
    (h1 : earlier xi ej iEnd jStart) (h2 : earlier xj ek jEnd kStart) :
    earlier xi ek iEnd kStart := by
  rcases h1 with hi | ⟨eq1,o1⟩
  · rcases h2 with hk | ⟨eq2,_⟩ <;> left <;> linarith
  · rcases h2 with hk | ⟨eq2,o2⟩
    · left; linarith
    · by_cases gap : ej < xj
      · left; linarith
      · have mid : ej=xj := le_antisymm hw (le_of_not_gt gap)
        rcases o1 with ie | js
        · right; exact ⟨by linarith, Or.inl ie⟩
        · rcases o2 with je | ks
          · exact (gap (hs js je)).elim
          · right; exact ⟨by linarith, Or.inr ks⟩

theorem equality_excluded_by_open_end (x : ℝ) (q : Prop) :
    earlier x x True q := Or.inr ⟨rfl, Or.inl trivial⟩

#print axioms closure_under_positive_middle
#print axioms equality_excluded_by_open_end
end Touching
