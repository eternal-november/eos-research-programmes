import Mathlib
namespace CoupledQueues
variable {V : Type}

def Covers (U A : Set V) (P : Set V → Prop) :=
  A ⊆ U ∧ P A

lemma left_restrict {A B U : Set V} (a : A ⊆ U)
    (agree : B ∩ U ⊆ A) : (A ∪ B) ∩ U = A := by
  ext v
  constructor
  · rintro ⟨hv, hu⟩
    rcases hv with hv | hv
    · exact hv
    · exact agree ⟨hv,hu⟩
  · intro hv
    exact ⟨Or.inl hv,a hv⟩

theorem exact_join {A B U W : Set V} {P Q : Set V → Prop}
    (a : A ⊆ U) (b : B ⊆ W)
    (agreeL : B ∩ U ⊆ A) (agreeR : A ∩ W ⊆ B)
    (validL : P A) (validR : Q B)
    (leastL : ∀ D, P (D ∩ U) → Q (D ∩ W) → A ⊆ D)
    (leastR : ∀ D, P (D ∩ U) → Q (D ∩ W) → B ⊆ D) :
    (P ((A ∪ B) ∩ U) ∧ Q ((A ∪ B) ∩ W)) ∧
    (∀ D, P (D ∩ U) → Q (D ∩ W) → A ∪ B ⊆ D) := by
  constructor
  · constructor
    · rw [left_restrict a agreeL]; exact validL
    · rw [Set.union_comm, left_restrict b agreeR]; exact validR
  · intro D p q v hv
    rcases hv with hv | hv
    · exact leastL D p q hv
    · exact leastR D p q hv

theorem budget_exact {C : Set V} {Law : Set V → Prop}
    {cost : Set V → Nat} (mono : Monotone cost)
    (least : ∀ D, Law D → C ⊆ D) (law : Law C) (permission : Set V) (k : Nat) :
    (∃ D, Law D ∧ D ⊆ permission ∧ cost D ≤ k) ↔
    C ⊆ permission ∧ cost C ≤ k := by
  constructor
  · rintro ⟨D, ok, allowed, bound⟩
    exact ⟨(least D ok).trans allowed, (mono (least D ok)).trans bound⟩
  · rintro ⟨ok, b⟩
    exact ⟨C, law, ok, b⟩

end CoupledQueues
#print axioms CoupledQueues.left_restrict
#print axioms CoupledQueues.exact_join
#print axioms CoupledQueues.budget_exact
