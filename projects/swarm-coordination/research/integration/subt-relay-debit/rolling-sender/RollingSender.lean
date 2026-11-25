import Mathlib
namespace RollingSender
def conflict (W t u : Nat) : Prop := t ≤ u ∧ u-t ≤ W
theorem impliedTriangle (W a b c : Nat) (ab : a ≤ b) (bc : b ≤ c)
    (ac : conflict W a c) : conflict W a b ∧ conflict W b c := by
  unfold conflict at *
  omega
theorem oppositeAfterTwo (a b c : Bool) (hab : a ≠ b) (hbc : b ≠ c) :
    a = c := by cases a <;> cases b <;> cases c <;> simp_all
theorem noThree (a b c : Bool) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : False :=
  hac (oppositeAfterTwo a b c hab hbc)
theorem forcedMiddleConflict (a m z : Bool) (ha : a=false) (hz : z=true)
    (hm1 : a ≠ m) (hm2 : m ≠ z) : False := by
  have e := oppositeAfterTwo a m z hm1 hm2
  simp_all
theorem middleCut (m : Nat) (h : m ≤ 6) :
    (¬ conflict 4 0 m) ↔ 4 < m := by
  unfold conflict
  omega
#print axioms impliedTriangle
#print axioms oppositeAfterTwo
#print axioms noThree
#print axioms forcedMiddleConflict
#print axioms middleCut
end RollingSender
