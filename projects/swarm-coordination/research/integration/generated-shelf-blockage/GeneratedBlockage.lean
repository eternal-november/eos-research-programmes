import Mathlib
namespace GeneratedBlockage
theorem guarded_departure {Cell : Type} (reservedAtMove unchangedNeed : Cell → Prop)
    (x : Cell) (cleared : ¬ reservedAtMove x)
    (monotone : ∀ y, unchangedNeed y → reservedAtMove y) :
    ¬ unchangedNeed x := fun h => cleared (monotone x h)

theorem no_observation_only_decider {History Observation : Type}
    (observe : History → Observation) (blocked : History → Prop)
    (left right : History) (same : observe left = observe right)
    (yes : blocked left) (no : ¬ blocked right) :
    ¬ ∃ classify : Observation → Prop, ∀ h, classify (observe h) ↔ blocked h := by
  rintro ⟨classify, exactness⟩
  have hx := (exactness left).2 yes
  rw [same] at hx
  exact no ((exactness right).1 hx)

theorem join_excludes_unwitnessed_notice
    {Event : Type} (notice stop : Event → Prop)
    (identityCause : ∀ e, notice e → stop e) :
    ¬ ∃ e, notice e ∧ ¬ stop e := by
  rintro ⟨e,h,n⟩
  exact n (identityCause e h)
end GeneratedBlockage
#print axioms GeneratedBlockage.guarded_departure
#print axioms GeneratedBlockage.no_observation_only_decider
#print axioms GeneratedBlockage.join_excludes_unwitnessed_notice
