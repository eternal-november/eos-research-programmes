import Mathlib

namespace PhaseRefinement

structure Prefix where
  tx : Nat
  rx : Nat
  callback : Bool

def absent : Prefix := ⟨0,0,false⟩
def transmittedWithoutArrival (b : Nat) : Prefix := ⟨b,0,false⟩

def nextFits (p : Prefix) (cap amount : Nat) (sameTx : Bool) : Prop :=
  (if sameTx then p.tx else 0)+amount ≤ cap

theorem callback_quotient_not_safe (a b cap : Nat)
    (hfit : a ≤ cap) (hexceed : cap < b+a) :
    absent.callback = (transmittedWithoutArrival b).callback ∧
    nextFits absent cap a true ∧
    ¬ nextFits (transmittedWithoutArrival b) cap a true := by
  exact ⟨rfl, by simpa [absent,nextFits], by simpa [transmittedWithoutArrival,nextFits] using hexceed⟩

theorem independent_sender_preserves_single_row (p : Prefix) (cap amount : Nat) :
    nextFits p cap amount false ↔ amount ≤ cap := by
  simp [nextFits]

theorem absent_cap_not_enough {α : Type} (worlds : Set α)
    (capacityQualified effectQualified : α → Prop)
    (w : α) (hw : w ∈ worlds) (noEffect : ¬ effectQualified w) :
    ¬ (∀ v ∈ worlds, capacityQualified v ∧ effectQualified v) :=
  fun h => noEffect (h w hw).2

#print axioms callback_quotient_not_safe
#print axioms independent_sender_preserves_single_row
#print axioms absent_cap_not_enough
end PhaseRefinement
