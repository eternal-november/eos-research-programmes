import Mathlib
namespace SilentStaging

def term (t r u : Nat) : Nat := r - (t-u)

theorem stageNeeded (t w d D b : Nat) (hb : b ≤ w) :
    t + (w - b) + d ≤ D ↔
      t + d ≤ D ∧ t+w+d-D ≤ b := by omega

theorem prefixNecessary (t r u pt pu : Nat)
    (hreq : r ≤ pt) (hmono : u ≤ t → pt ≤ pu + (t-u))
    (hearlier : t ≤ u → pt ≤ pu) :
    term t r u ≤ pu := by
  unfold term
  by_cases h : u ≤ t
  · have h' := hmono h
    omega
  · have h' := hearlier (by omega)
    omega

theorem termStep (t r u : Nat) :
    term t r u ≤ term t r (u+1) ∧ term t r (u+1) ≤ term t r u + 1 := by
  unfold term
  omega

theorem termBound (t r u w : Nat) (h1 : r ≤ t) (h2 : r ≤ w) :
    term t r u ≤ u ∧ term t r u ≤ w := by
  unfold term
  omega

theorem maxTermStep (a b a' b' : Nat)
    (ha : a ≤ a') (hb : b ≤ b') (ha' : a' ≤ a+1) (hb' : b' ≤ b+1) :
    max a b ≤ max a' b' ∧ max a' b' ≤ max a b + 1 := by
  constructor
  · exact max_le (le_trans ha (le_max_left _ _)) (le_trans hb (le_max_right _ _))
  · apply max_le
    · exact le_trans ha' (Nat.add_le_add_right (le_max_left _ _) 1)
    · exact le_trans hb' (Nat.add_le_add_right (le_max_right _ _) 1)

#print axioms stageNeeded
#print axioms prefixNecessary
#print axioms termStep
#print axioms termBound
#print axioms maxTermStep
end SilentStaging
