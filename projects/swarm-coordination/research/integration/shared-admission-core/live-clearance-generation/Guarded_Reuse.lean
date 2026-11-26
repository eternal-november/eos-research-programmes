import Mathlib

namespace GuardedReuse

def law (now arrive issued current : Nat) (clear numbered : Bool) : Prop :=
  arrive ≤ now ∧ clear = true ∧ (numbered = false ∨ issued = current)

theorem fresh_occupancy_not_enough (ready now a b : Nat) (distinct : a ≠ b) :
    ¬ law now ready a b true true := by
  simp [law,distinct]

theorem seen_receipt_not_clearance (ready now epoch : Nat) :
    ¬ law now ready epoch epoch false false := by
  simp [law]

theorem least_causal_cut (ready : ℕ → Prop) [DecidablePred ready] (due : ℕ)
    (possible : ∃ t, t ≤ due ∧ ready t) :
    ∃ t, t ≤ due ∧ ready t ∧ ∀ u < t, ¬ ready u := by
  let h : ∃ t, ready t := by
    obtain ⟨t,_,hr⟩ := possible
    exact ⟨t,hr⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h, ?_⟩
  · obtain ⟨v,hv,hready⟩ := possible
    exact le_trans (Nat.find_min' h hready) hv
  · intro u hu
    exact Nat.find_min h hu

#print axioms fresh_occupancy_not_enough
#print axioms seen_receipt_not_clearance
#print axioms least_causal_cut
end GuardedReuse
