import Mathlib
namespace WatchedWindows

theorem interval_difference (a b c d x : ℤ) :
    ((a ≤ x ∧ x ≤ b) ∧ ¬ (c ≤ x ∧ x ≤ d)) ↔
      (a ≤ x ∧ x ≤ min b (c - 1)) ∨ (max a (d + 1) ≤ x ∧ x ≤ b) := by
  simp only [le_min_iff, max_le_iff]
  omega

theorem removing_one_alternative {Key : Type} (k : Key)
    (watch good good' : Key → Prop)
    (outside : ∀ j, j ≠ k → (good j ↔ good' j))
    (removed : ¬ good' k) :
    (∃ j, watch j ∧ good' j) ↔ ∃ j, j ≠ k ∧ watch j ∧ good j := by
  constructor
  · rintro ⟨j, hw, hg⟩
    have hne : j ≠ k := by
      intro h
      subst j
      exact removed hg
    exact ⟨j,hne,hw,(outside j hne).mpr hg⟩
  · rintro ⟨j,hne,hw,hg⟩
    exact ⟨j,hw,(outside j hne).mp hg⟩

theorem not_valid_after_new_epoch (e e' : ℕ) (h : e < e') (physicallyUsable : Prop) :
    ¬ (e = e' ∧ physicallyUsable) := by
  exact fun g => Nat.ne_of_lt h g.1

#print axioms interval_difference
#print axioms removing_one_alternative
#print axioms not_valid_after_new_epoch
end WatchedWindows
