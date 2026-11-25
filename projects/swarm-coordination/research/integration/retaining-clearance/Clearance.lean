import Mathlib

namespace SwarmRetention

theorem common_action {Resource State : Type} (room : Resource → Prop)
    (occupied : State → Resource → Prop) (cell : State → Prop) :
    (∃ a, room a ∧ ∀ b, cell b → ¬ occupied b a) ↔
    (∃ a, room a ∧ ¬ ∃ b, cell b ∧ occupied b a) := by
  constructor
  · rintro ⟨a, ha, hc⟩
    refine ⟨a, ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hc b hb hab
  · rintro ⟨a, ha, hn⟩
    exact ⟨a, ha, fun b hb hab => hn ⟨b, hb, hab⟩⟩

theorem coded_choice {Resource : Type} (B C Y : Resource → Prop)
    (hBC : ∀ x, B x → C x) (h : ∃ x, Y x ∧ ¬ C x) :
    ∃ x, Y x ∧ ¬ B x := by
  obtain ⟨x, hy, hc⟩ := h
  exact ⟨x, hy, fun hb => hc (hBC x hb)⟩

theorem hidden_reentry {Resource : Type} (B Y : Resource → Prop) :
    ¬ ∃ x, Y x ∧ ¬ B x ∧ ∀ e, ¬ B e → x ≠ e := by
  rintro ⟨x, _, hB, he⟩
  exact he x hB rfl

theorem visible_conflict {Resource : Type} (B C Y : Resource → Prop)
    (e : Resource) (hY : ∀ x, Y x → B x ∨ C x ∨ x = e) :
    ¬ ∃ x, Y x ∧ ¬ B x ∧ ¬ C x ∧ x ≠ e := by
  rintro ⟨x, hy, hb, hc, he⟩
  rcases hY x hy with h | h | h
  · exact hb h
  · exact hc h
  · exact he h
end SwarmRetention

#print axioms SwarmRetention.common_action
#print axioms SwarmRetention.coded_choice
#print axioms SwarmRetention.hidden_reentry
#print axioms SwarmRetention.visible_conflict
