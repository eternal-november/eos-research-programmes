import Lean

namespace WeightedHandoff
theorem shared_port (t P a b : Nat) (ha : 0 < a) (h : a ≤ P) :
    ((t+a < t+P+a) ∧ (t+P < t+a+b)) ↔ P < a+b := by
  omega

def clip (D t : Nat) : Option Nat := if t ≤ D then some t else none
def addCap (D : Nat) (a b : Option Nat) : Option Nat :=
  match a,b with
  | some u, some v => clip D (u+v)
  | _,_ => none

theorem clip_add (D a b : Nat) : addCap D (clip D a) (clip D b) = clip D (a+b) := by
  by_cases ha : a≤D
  · by_cases hb : b≤D
    · simp [addCap, clip, ha, hb]
    · have hz : ¬a+b≤D := by omega
      simp [addCap, clip, ha, hb, hz]
  · have hz : ¬a+b≤D := by omega
    simp [addCap,clip,ha,hz]

#print axioms shared_port
#print axioms clip_add
end WeightedHandoff
