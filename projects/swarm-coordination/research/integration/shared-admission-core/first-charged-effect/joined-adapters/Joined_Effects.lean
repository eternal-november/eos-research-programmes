import Mathlib

namespace JoinedEffects

/-- A shared candidate, not two unrelated existential witnesses. -/
theorem compatible_choice {X : Type} (R P : X → Prop) :
    (∃ x, R x ∧ P x) → (∃ x, R x) ∧ (∃ x, P x) := by
  rintro ⟨x, hr, hp⟩
  exact ⟨⟨x, hr⟩, ⟨x, hp⟩⟩

theorem separate_not_enough :
    (∃ x : Bool, x = true) ∧ (∃ x : Bool, x = false) ∧
    ¬ (∃ x : Bool, x = true ∧ x = false) := by
  refine ⟨⟨true, rfl⟩, ⟨false, rfl⟩, ?_⟩
  rintro ⟨x, h, hf⟩
  rw [h] at hf
  contradiction

/-- Checking at different calls is allowed only with a frame for both uses. -/
theorem settlement_at_held_cut {X : Type} {x : X}
    {Rcheck Pcheck Ruse Puse : X → Prop}
    (radioFrame : Rcheck x → Ruse x)
    (physicalFrame : Pcheck x → Puse x)
    (observed : Rcheck x ∧ Pcheck x) : Ruse x ∧ Puse x :=
  ⟨radioFrame observed.1, physicalFrame observed.2⟩

end JoinedEffects
