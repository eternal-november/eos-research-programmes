import Mathlib

namespace StagedCommit

theorem robust_requires_pair {A : Type} [DecidableEq A]
    (p : Finset A) (a b : A) (different : a ≠ b)
    (onlyA : ∃ x ∈ p, x = a) (onlyB : ∃ x ∈ p, x = b) :
    2 ≤ p.card := by
  have ha : a ∈ p := by obtain ⟨x,h,e⟩ := onlyA; exact e ▸ h
  have hb : b ∈ p := by obtain ⟨x,h,e⟩ := onlyB; exact e ▸ h
  have sub : ({a,b} : Finset A) ⊆ p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with e|e
    · exact e ▸ ha
    · exact e ▸ hb
  have h := Finset.card_le_card sub
  simpa [different] using h

theorem both_prepared_survive_one_loss {A : Type} [DecidableEq A]
    (a b fail : A) (h : a ≠ b) :
    ∃ x ∈ ({a,b} : Finset A), x ≠ fail := by
  by_cases e : a = fail
  · refine ⟨b,by simp,?_⟩
    intro h'
    exact h (e.trans h'.symm)
  · exact ⟨a,by simp,e⟩

theorem accepted_scope_contains_operation (t h ready expiry old last k : ℕ)
    (start : ready ≤ t) (H : t+h ≤ min expiry (min old last))
    (live : t ≤ k ∧ k < t+h) :
    ready ≤ k ∧ k < expiry ∧ k < old ∧ k < last := by
  omega

theorem stale_blocks_finished_operation (cut h expiry : ℕ)
    (hc : expiry < cut+h) : ¬ cut+h ≤ expiry := by omega

#print axioms robust_requires_pair
#print axioms both_prepared_survive_one_loss
#print axioms accepted_scope_contains_operation
#print axioms stale_blocks_finished_operation
end StagedCommit
