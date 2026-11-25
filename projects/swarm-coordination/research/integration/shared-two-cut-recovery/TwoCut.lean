import Mathlib

namespace TwoCut

theorem factor {H V P O A : Type} (view : H → V)
    (observe : H → P → O) (law : H → P → A → Prop) :
    (∃ first : V → P, ∃ next : V → O → A,
      ∀ h, law h (first (view h)) (next (view h) (observe h (first (view h))))) ↔
    (∀ v, ∃ p, ∀ o, ∃ a, ∀ h, view h = v → observe h p = o → law h p a) := by
  constructor
  · rintro ⟨first, next, works⟩ v
    refine ⟨first v, fun o => ⟨next v o, ?_⟩⟩
    intro h hv ho
    simpa only [hv, ho] using works h
  · intro h
    classical
    choose p hp using h
    choose a ha using hp
    exact ⟨p, a, fun z => ha (view z) (observe z (p (view z))) z rfl rfl⟩

theorem incompatible_observation {H P O A : Type} (observe : H → P → O)
    (law : H → P → A → Prop) (p : P) (x y : H)
    (same : observe x p = observe y p) (bad : ∀ a, law x p a → ¬ law y p a) :
    ¬ ∃ next : O → A, ∀ h, law h p (next (observe h p)) := by
  rintro ⟨next, w⟩
  have hx := w x
  rw [same] at hx
  exact (bad (next (observe y p)) hx) (w y)

end TwoCut

#print axioms TwoCut.factor
#print axioms TwoCut.incompatible_observation
