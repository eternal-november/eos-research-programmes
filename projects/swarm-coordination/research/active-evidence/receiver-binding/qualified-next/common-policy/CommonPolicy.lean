import Mathlib

theorem factorThroughKey {W K A : Type*} (key : W → K) (act : W → A) (default : A) :
    (∃ policy : K → A, ∀ w, policy (key w) = act w) ↔
      ∀ w v, key w = key v → act w = act v := by
  constructor
  · rintro ⟨policy,h⟩ w v e
    rw [← h w, ← h v, e]
  · intro single
    classical
    let policy (k : K) : A :=
      if h : ∃ w, key w = k then act (Classical.choose h) else default
    refine ⟨policy, ?_⟩
    intro w
    have present : ∃ v, key v = key w := ⟨w,rfl⟩
    simp only [policy, dite_eq_left present]
    exact single _ _ (Classical.choose_spec present)

#print axioms factorThroughKey
