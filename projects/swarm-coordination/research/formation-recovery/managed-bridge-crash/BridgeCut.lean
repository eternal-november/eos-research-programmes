import Mathlib
namespace BridgeCut

theorem arrival_lower_bound (s R V t final leftMove rightMove : ℝ)
    (hV : 0 < V) (hfinal : final ≤ R)
    (hleft : leftMove ≤ V*t) (hright : rightMove ≤ V*t)
    (triangleBound : s ≤ leftMove + final + rightMove) :
    (s-R)/(2*V) ≤ t := by
  apply (div_le_iff₀ (by positivity : 0 < 2*V)).2
  linarith

theorem clipped_body_obstruction (eps x y : ℝ)
    (hx : x^2 ≤ eps^2) (hy : y^2 ≤ 4*eps)
    (hsmall : eps^2 + 4*eps < 1/4) :
    x^2 + y^2 < 1/4 := by linarith

end BridgeCut
#print axioms BridgeCut.arrival_lower_bound
#print axioms BridgeCut.clipped_body_obstruction
