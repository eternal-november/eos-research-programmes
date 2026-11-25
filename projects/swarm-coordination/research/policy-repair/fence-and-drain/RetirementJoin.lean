import Mathlib
namespace RetirementJoin

theorem coverage_of_old_effects {Scope : Type} {s t : Scope}
    (same : s = t) {last doneUntil : ℕ} (covered : last ≤ doneUntil)
    (settled : Scope → ℕ → Prop)
    (closed : ∀ i, 0 < i → i ≤ doneUntil → settled t i) :
    ∀ i, 0 < i → i ≤ last → settled s i := by
  subst s
  intro i pos hi
  exact closed i pos (hi.trans covered)

theorem exact_on_opaque_prefix (n c : ℕ) :
    (∀ i, 0 < i → i ≤ n → i ≤ c) ↔ n ≤ c := by
  constructor
  · intro covers
    by_cases pos : 0 < n
    · exact covers n pos le_rfl
    · omega
  · intro covers i _ h
    exact h.trans covers

theorem exact_deferral_saving (prepared ready : ℕ) :
    (ready + prepared + 1) - (max prepared ready + 1) =
      min prepared ready := by
  rcases le_total prepared ready with h | h
  · simp [max_eq_right h, min_eq_left h]
  · simp [max_eq_left h, min_eq_right h]

theorem early_prefix_may_be_extended :
    (∀ i : ℕ, 0 < i → i ≤ 1 → i ≤ 1) ∧
    ¬ (∀ i : ℕ, 0 < i → i ≤ 2 → i ≤ 1) := by
  refine ⟨fun _ _ hi => hi, ?_⟩
  intro h
  have := h 2 (by decide) (by decide)
  omega

#print axioms coverage_of_old_effects
#print axioms exact_on_opaque_prefix
#print axioms exact_deferral_saving
#print axioms early_prefix_may_be_extended
end RetirementJoin
