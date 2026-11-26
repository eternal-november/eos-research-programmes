import Lean
namespace ConditionalRebind

theorem same_observation_no_common_edit {World Obs : Type*}
    (see : World → Obs) (mustRebind : World → Bool) (a b : World)
    (same : see a = see b) (different : mustRebind a ≠ mustRebind b) :
    ¬ ∃ choose : Obs → Bool, ∀ w, choose (see w) = mustRebind w := by
  rintro ⟨p,h⟩
  exact different ((h a).symm.trans ((congrArg p same).trans (h b)))

theorem local_strict_cut (k : Nat) : (2+k < 5) ↔ k ≤ 2 := by omega
theorem armed_strict_cut (q : Nat) (positive : 0 < q) :
    (3+q < 5) ↔ q = 1 := by omega
theorem witness_gap : ¬ (2+4 < (5 : Nat)) ∧ 3+1 < (5 : Nat) := by decide

#print axioms same_observation_no_common_edit
#print axioms local_strict_cut
#print axioms armed_strict_cut
#print axioms witness_gap
end ConditionalRebind
