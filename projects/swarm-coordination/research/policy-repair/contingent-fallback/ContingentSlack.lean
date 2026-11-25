import Mathlib
namespace ContingentSlack

theorem source_class_common_edges {World Duty Helper : Type}
    (E : World → Duty → Helper → Prop) (p : Duty → Helper) :
    (∀ w j, E w j (p j)) ↔ (∀ j, ∀ w, E w j (p j)) := by
  constructor
  · intro h j w
    exact h w j
  · intro h w j
    exact h j w

theorem action_present_in_every_class {S T A : Type}
    (ok : S → A → Prop) (view : S → T) :
    (∃ p : T → A, ∀ x, ok x (p (view x))) ↔
      (∀ z, ∃ a, ∀ x, view x = z → ok x a) := by
  classical
  constructor
  · rintro ⟨p,h⟩ z
    refine ⟨p z,?_⟩
    intro x hx
    simpa [hx] using h x
  · intro h
    exact ⟨fun z => Classical.choose (h z),
      fun x => Classical.choose_spec (h (view x)) x rfl⟩

theorem old_count_remains (current tails : Nat)
    (retired : 0 < tails) :
    (current+tails)-1 = current+(tails-1) := by omega

theorem receipt_can_bind_interval
    (cut start finish lockEnd read : Nat)
    (lockstart : cut ≤ start)
    (held : finish ≤ lockEnd) (event : start ≤ read ∧ read < finish) :
    cut ≤ read ∧ read < lockEnd := by omega

end ContingentSlack
#print axioms ContingentSlack.source_class_common_edges
#print axioms ContingentSlack.action_present_in_every_class
#print axioms ContingentSlack.old_count_remains
#print axioms ContingentSlack.receipt_can_bind_interval
