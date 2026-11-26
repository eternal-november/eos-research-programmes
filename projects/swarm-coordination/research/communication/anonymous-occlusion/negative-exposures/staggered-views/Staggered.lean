import Mathlib

namespace Staggered

theorem erodedCovered (w m left right h x : ℚ)
    (a : -w ≤ x) (b : x ≤ w)
    (ml : left ≤ m) (mr : right ≤ m)
    (overlap : left+right ≤ h) :
    (-w-m+left ≤ x ∧ x ≤ h/2-left) ∨
    (-h/2+right ≤ x ∧ x ≤ w+m-right) := by
  by_cases q : x ≤ h/2-left
  · exact Or.inl ⟨by linarith, q⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem missedCenterWitness (h radius : ℚ) (small : h < 2*radius) :
    h/2 < radius ∧ -radius < -h/2 := by constructor <;> linarith

theorem inconsistentPredecessors (x y : ℚ)
    (left : x < -1) (right : 1/2 < y) : 1 < y-x := by linarith

theorem retrospectiveNotAvailable (earlier older newest : ℚ)
    (late : earlier < newest) : ¬ (max older newest ≤ earlier) := by
  intro h
  exact not_lt_of_ge ((le_max_right older newest).trans h) late

end Staggered

#print axioms Staggered.erodedCovered
#print axioms Staggered.missedCenterWitness
#print axioms Staggered.inconsistentPredecessors
#print axioms Staggered.retrospectiveNotAvailable
