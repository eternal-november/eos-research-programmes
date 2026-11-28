import Mathlib

namespace ServiceProfile
variable {A : Type} [DecidableEq A]

def equivalent (cap : Nat) (s t : Finset A) : Prop :=
  ∀ u : Finset A, u.card ≤ cap → (s ⊆ u ↔ t ⊆ u)

theorem exact (cap : Nat) (s t : Finset A) :
    equivalent cap s t ↔ (s = t ∨ (cap < s.card ∧ cap < t.card)) := by
  constructor
  · intro h
    by_cases hs : s.card ≤ cap
    · have hts : t ⊆ s := (h s hs).1 Finset.Subset.rfl
      have ht : t.card ≤ cap := (Finset.card_le_card hts).trans hs
      have hst : s ⊆ t := (h t ht).2 Finset.Subset.rfl
      exact Or.inl (Finset.Subset.antisymm hst hts)
    · by_cases ht : t.card ≤ cap
      · have hst : s ⊆ t := (h t ht).2 Finset.Subset.rfl
        exact False.elim (hs ((Finset.card_le_card hst).trans ht))
      · exact Or.inr ⟨Nat.lt_of_not_ge hs, Nat.lt_of_not_ge ht⟩
  · rintro (rfl | ⟨hs, ht⟩) u hu
    · rfl
    · constructor <;> intro h
      · exact False.elim ((Nat.not_le_of_gt hs) ((Finset.card_le_card h).trans hu))
      · exact False.elim ((Nat.not_le_of_gt ht) ((Finset.card_le_card h).trans hu))

theorem smaller_partner_scope {b c : Nat} (h : b ≤ c) (s t : Finset A)
    (q : equivalent c s t) : equivalent b s t :=
  fun u hu => q u (hu.trans h)

theorem exposing_comparison_failure {b c : Nat} (s t : Finset A)
    (hs : b < s.card) (ht : b < t.card) (hsc : s.card ≤ c) (hts : ¬ t ⊆ s) :
    equivalent b s t ∧ ¬ equivalent c s t := by
  constructor
  · exact (exact b s t).2 (Or.inr ⟨hs, ht⟩)
  · intro h
    exact hts ((h s hsc).1 Finset.Subset.rfl)

end ServiceProfile
