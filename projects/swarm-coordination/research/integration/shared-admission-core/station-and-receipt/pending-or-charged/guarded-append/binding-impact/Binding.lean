import Mathlib
open scoped BigOperators
namespace BindingImpact

theorem fanout_delta {ι : Type} (front : Finset ι)
    (bytes fanout changed : ι → Nat) :
    (∑ i ∈ front, bytes i * (fanout i + changed i)) =
    (∑ i ∈ front, bytes i * fanout i) +
    (∑ i ∈ front, bytes i * changed i) := by
  simp only [Nat.mul_add, Finset.sum_add_distrib]

theorem latest_is_enough (early late lim : Nat)
    (h : early ≤ late) (ok : late ≤ lim) : early ≤ lim := by omega

theorem jointly_safe (a b deltaA deltaB capA capB : Nat) :
    (a + deltaA ≤ capA ∧ b + deltaB ≤ capB) ↔
      (∀ k : Bool, (if k then a + deltaA else b + deltaB) ≤
        (if k then capA else capB)) := by
  constructor
  · intro h k
    cases k
    · simpa using h.2
    · simpa using h.1
  · intro h
    exact ⟨by simpa using h true, by simpa using h false⟩

#print axioms fanout_delta
#print axioms latest_is_enough
#print axioms jointly_safe
end BindingImpact
