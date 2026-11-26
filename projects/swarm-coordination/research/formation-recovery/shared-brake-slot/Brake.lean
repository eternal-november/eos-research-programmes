import Mathlib

namespace SharedBrake

/-- With equal initial velocities, the first two exclusive brake slots
must spend at least one unit of link or clearance slack. -/
theorem firstTwo (frontFirst frontSecond : Bool) :
    let a : Int := if frontFirst then -1 else 1
    let b : Int := if frontSecond then -1 else 1
    2 ≤ (3*a+b).natAbs := by
  cases frontFirst <;> cases frontSecond <;> decide

theorem parityIdentity (v positiveWeights : Int) :
    (2 * positiveWeights - v*(2*v+1)) % 2 = v % 2 := by
  have h : 2 * positiveWeights - v*(2*v+1)
      = 2 * (positiveWeights - v*v - v) + v := by ring
  rw [h]
  omega

/-- Two slots of opposite assignment restore zero relative velocity and
move exactly one unit toward the first selected signed side. -/
theorem pairStep (gap a : ℚ) :
    gap + a/2 + a - a/2 = gap+a := by ring

theorem gapAndTotalDetermineDistances (f r total gap : ℚ)
    (h0 : f+r=total) (h1 : f-r=gap) :
    f=(total+gap)/2 ∧ r=(total-gap)/2 := by constructor <;> linarith

end SharedBrake

#print axioms SharedBrake.firstTwo
#print axioms SharedBrake.parityIdentity
#print axioms SharedBrake.pairStep
#print axioms SharedBrake.gapAndTotalDetermineDistances
