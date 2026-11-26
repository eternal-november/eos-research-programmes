import Mathlib

namespace RecurringMasks

abbrev Mask := Finset ℕ

/-- Walk indices store the union of the justice labels, not their order. -/
inductive Walk {V : Type} (edge : V → V → Mask → Prop) : V → V → Mask → Prop where
  | nil (a : V) : Walk edge a a ∅
  | cons {a b c : V} {m n : Mask} :
      edge a b m → Walk edge b c n → Walk edge a c (m ∪ n)

theorem append {V : Type} {edge : V → V → Mask → Prop}
    {a b c : V} {m n : Mask} (p : Walk edge a b m) (q : Walk edge b c n) :
    Walk edge a c (m ∪ n) := by
  induction p with
  | nil => simpa using q
  | cons e _ ih =>
    rw [Finset.union_assoc]
    exact Walk.cons e (ih q)

/-- The common endpoint can be revisited once per requested color. -/
theorem closed_cover (good : Mask → Prop) (J : Mask)
    (empty : good ∅) (join : ∀ a b, good a → good b → good (a ∪ b))
    (witness : ∀ j ∈ J, ∃ m, good m ∧ j ∈ m) :
    ∃ m, good m ∧ J ⊆ m := by
  induction J using Finset.induction_on with
  | empty => exact ⟨∅, empty, Finset.empty_subset _⟩
  | @insert j J hj ih =>
    obtain ⟨p,hp,hj'⟩ := witness j (by simp)
    obtain ⟨q,hq,hJ⟩ := ih (fun k hk => witness k (Finset.mem_insert_of_mem hk))
    refine ⟨p ∪ q, join p q hp hq, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | h
    · exact Finset.mem_union.mpr (Or.inl hj')
    · exact Finset.mem_union.mpr (Or.inr (hJ h))

theorem common_cut {V : Type} {edge : V → V → Mask → Prop} (x : V) (J : Mask)
    (witness : ∀ j ∈ J, ∃ m, Walk edge x x m ∧ j ∈ m) :
    ∃ m, Walk edge x x m ∧ J ⊆ m :=
  closed_cover _ J (Walk.nil _) (fun _ _ p q => append p q) witness

#print axioms append
#print axioms closed_cover
#print axioms common_cut
end RecurringMasks
