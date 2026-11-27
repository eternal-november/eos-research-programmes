import Mathlib
namespace DensityAtRest

theorem clippedSuffix {x a cap D : ℝ}
    (hx : 0 ≤ x) (hD : 0 ≤ D) (hc : 0 ≤ cap) (ha : a ≤ cap)
    (hd : x+a ≤ D) :
    let y := max 0 (x+a)
    0 ≤ y ∧ y ≤ D ∧ a ≤ y-x ∧ y-x ≤ cap := by
  dsimp
  constructor
  · exact le_max_left _ _
  constructor
  · exact max_le hD hd
  constructor
  · have h := le_max_right (0:ℝ) (x+a)
    linarith
  · have h := max_le (by linarith : (0:ℝ) ≤ x+cap) (by linarith : x+a≤x+cap)
    linarith

theorem mergedPositiveWeights {a b c delta D : ℝ}
    (Dlarge : delta ≤ D) (aPos : D < a) (bPos : D < b)
    (carry : a+b-delta ≤ c) :
    max 0 (a-D) + max 0 (b-D) ≤ max 0 (c-D) := by
  have ca : 0 ≤ a-D := by linarith
  have cb : 0 ≤ b-D := by linarith
  rw [max_eq_right ca,max_eq_right cb]
  have right := le_max_right (0:ℝ) (c-D)
  linarith

theorem intervalDeficitNecessary {oldSum requirement before after reach : ℝ}
    (h0 : 0≤before) (h1 : after≤reach)
    (safe : requirement ≤ oldSum + after-before) :
    requirement-reach ≤ oldSum := by linarith

theorem centeredPrefix {x total : ℝ} (hx : 0 ≤ x) (ht : x ≤ total) :
    -(total/2) ≤ x-total/2 ∧ x-total/2 ≤ total/2 := by
  constructor <;> linarith

#print axioms clippedSuffix
#print axioms mergedPositiveWeights
#print axioms intervalDeficitNecessary
#print axioms centeredPrefix
end DensityAtRest
