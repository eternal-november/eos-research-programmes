import Mathlib
namespace ArtifactReplay
def finishedView (queried : Nat) (accepted : List Nat) : Nat × Nat × Bool :=
  (queried, accepted.length, false)
theorem closedMembershipFailure :
    finishedView 7 [7, 9] = finishedView 7 [8, 9] ∧
    7 ∈ ([7, 9] : List Nat) ∧ 7 ∉ ([8, 9] : List Nat) := by decide
theorem finishedCannotDecide (dec : Nat × Nat × Bool → Bool)
    (h : ∀ (r : Nat) (before : List Nat),
        dec (finishedView r before) = decide (r ∈ before)) : False := by
  have x := h 7 [7, 9]
  have y := h 7 [8, 9]
  rw [closedMembershipFailure.1] at x
  rw [x] at y
  simp at y

def copyClear (before inside after : List Nat) : List Nat :=
  (before ++ inside).take before.length ++ after
def detach (before inside after : List Nat) : List Nat :=
  before ++ (inside ++ after)
theorem lostCount (b i a : List Nat) :
    (b ++ i ++ a).length - (copyClear b i a).length = i.length := by
  simp [copyClear]
  omega
theorem detachInOrder (b i a : List Nat) : detach b i a = b ++ i ++ a := by
  simp [detach,List.append_assoc]
#print axioms closedMembershipFailure
#print axioms finishedCannotDecide
#print axioms lostCount
#print axioms detachInOrder
end ArtifactReplay
