import Mathlib

namespace GateBudget

-- The two length tests are on the receiver. An attempted Q that is
-- rejected contributes nothing to RX; P's already accepted bytes stay.
def qb (a b q r : Nat) : Prop :=
  a ≤ q ∧ a+b ≤ r ∧ (2*a ≤ q → 2*a+b ≤ r)

def bq (a b q r : Nat) : Prop :=
  a+b ≤ r ∧ a+b ≤ q

def exactRead (a b q r : Nat) : Prop :=
  a ≤ q ∧ a+b ≤ r

theorem no_fixed_order_strip (a b q r : Nat)
    (base : exactRead a b q r) :
    ¬ (qb a b q r ∨ bq a b q r) ↔
    2*a ≤ q ∧ q < a+b ∧ r < 2*a+b := by
  unfold exactRead at base
  unfold qb bq
  omega

theorem observationCannotRescueEarlierCut (firstArrival readCost close : Nat)
    (h : close ≤ firstArrival + readCost) :
    ∀ issue : Nat, firstArrival + readCost ≤ issue → ¬ (issue < close) := by
  omega

theorem narrowInterference :
    exactRead 9 10 18 19 ∧ ¬ (qb 9 10 18 19 ∨ bq 9 10 18 19) := by
  unfold exactRead qb bq
  omega

theorem bothNeighborsWork :
    qb 9 10 17 19 ∧ bq 9 10 19 19 := by
  unfold qb bq
  omega

#print axioms no_fixed_order_strip
#print axioms observationCannotRescueEarlierCut
#print axioms narrowInterference
#print axioms bothNeighborsWork
end GateBudget
