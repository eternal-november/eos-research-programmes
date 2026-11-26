import Mathlib
namespace MonotoneChain
/-- Subtracting the overlap of two tight spans leaves too little room for the outer pair. -/
theorem overlapping_ties_impossible (a p q xL xI xJ xR : ℝ)
    (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) (hij : xI ≤ xJ)
    (hL : 4*a*(xJ-xL) = p^2) (hR : 4*a*(xR-xI) = q^2)
    (hspan : (p+q)^2 ≤ 4*a*(xR-xL)) : False := by
  have hgap := mul_nonneg (show 0 ≤ 4*a by positivity) (sub_nonneg.mpr hij)
  linarith [mul_pos hp hq, show 4*a*(xR-xL) =
    4*a*(xJ-xL) + 4*a*(xR-xI) - 4*a*(xJ-xI) by ring,
    show (p+q)^2 = p^2+q^2+2*(p*q) by ring]

theorem tie_propagates (a q xI xJ xK : ℝ)
    (ha : 0 < a) (hij : xI ≤ xJ)
    (hJ : q^2 ≤ 4*a*(xK-xJ)) (hI : 4*a*(xK-xI) = q^2) :
    xI = xJ := by
  have hh : 4*a*(xJ-xI) ≤ 0 := by linarith [show
    4*a*(xJ-xI) = 4*a*(xK-xI) - 4*a*(xK-xJ) by ring]
  by_contra h
  exact (not_lt_of_ge hh) (mul_pos (by positivity) (sub_pos.mpr (lt_of_le_of_ne hij h)))

#print axioms overlapping_ties_impossible
#print axioms tie_propagates
end MonotoneChain
