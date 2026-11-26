import Mathlib

namespace NegativeFrames

theorem noHiddenClosedBand (a b entry exit vmax width : ℚ)
    (positive : 0 < vmax)
    (after : a < entry) (before : exit < b)
    (trip : width ≤ vmax * (exit - entry))
    (noRoom : vmax * (b-a) ≤ width) : False := by
  have short : exit - entry < b-a := by linarith
  have hp := mul_lt_mul_of_pos_left short positive
  linarith

theorem sharedClockOffsetCancels (a b offset : ℚ) :
    b + offset - (a + offset) = b-a := by ring

theorem independentOffsetsBudget (nominal first last j : ℚ)
    (l : -j ≤ first) (u : last ≤ j) :
    nominal + last - first ≤ nominal + 2*j := by linarith

theorem independentOffsetsTight (nominal j : ℚ) :
    nominal + j - (-j) = nominal + 2*j := by ring

end NegativeFrames

#print axioms NegativeFrames.noHiddenClosedBand
#print axioms NegativeFrames.sharedClockOffsetCancels
#print axioms NegativeFrames.independentOffsetsBudget
#print axioms NegativeFrames.independentOffsetsTight
