import Mathlib

theorem incoming_boundary_sparse {V : Type*}
    (keep reached : V → Prop) (old new : V → V → Prop)
    (retainedOld : ∀ x, keep x → reached x)
    (oldClosed : ∀ x y, reached x → old x y → reached y)
    (v : V) :
    (∃ u, keep u ∧ new u v) ↔
      ((reached v ∧ ∃ u, keep u ∧ new u v) ∨
       ∃ u, keep u ∧ new u v ∧ ¬ old u v) := by
  constructor
  · rintro ⟨u, hu, e⟩
    by_cases o : old u v
    · exact Or.inl ⟨oldClosed u v (retainedOld u hu) o, ⟨u, hu, e⟩⟩
    · exact Or.inr ⟨u, hu, e, o⟩
  · rintro (⟨_, w⟩ | ⟨u, hu, e, _⟩)
    · exact w
    · exact ⟨u, hu, e⟩

#print axioms incoming_boundary_sparse
