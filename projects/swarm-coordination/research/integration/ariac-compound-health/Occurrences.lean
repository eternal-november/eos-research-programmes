import Mathlib

def down {E R : Type} (affects : E → R → Prop) (active : Finset E) (r : R) : Prop :=
  ∃ e ∈ active, affects e r

theorem other_blocker_survives {E R : Type} [DecidableEq E]
    (affects : E → R → Prop) (active : Finset E) (cut other : E) (r : R)
    (hm : other ∈ active) (hd : other ≠ cut) (ha : affects other r) :
    down affects (active.erase cut) r :=
  ⟨other, Finset.mem_erase.mpr ⟨hd, hm⟩, ha⟩

theorem down_after_merge {E R : Type} [DecidableEq E]
    (affects : E → R → Prop) (a b : Finset E) (r : R) :
    down affects (a ∪ b) r ↔ down affects a r ∨ down affects b r := by
  unfold down
  constructor
  · intro h
    rcases h with ⟨e, he, hr⟩
    rcases Finset.mem_union.mp he with he | he
    · exact Or.inl ⟨e, he, hr⟩
    · exact Or.inr ⟨e, he, hr⟩
  · intro h
    rcases h with ⟨e, he, hr⟩ | ⟨e, he, hr⟩
    · exact ⟨e, Finset.mem_union.mpr (Or.inl he), hr⟩
    · exact ⟨e, Finset.mem_union.mpr (Or.inr he), hr⟩

theorem scope_unaffected {E R : Type} (affects : E → R → Prop)
    (active : Finset E) (r : R) (h : ∀ e ∈ active, ¬ affects e r) :
    ¬ down affects active r := by
  rintro ⟨e, he, hr⟩
  exact h e he hr

#print axioms other_blocker_survives
#print axioms down_after_merge
#print axioms scope_unaffected
