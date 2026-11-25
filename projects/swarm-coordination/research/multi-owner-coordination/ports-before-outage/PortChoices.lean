import Mathlib
namespace PortChoices
theorem protocol_iff {W Q R M P : Type} (q : W → Q) (r : W → R)
    (enc : Q → M) (ok : W → P → Prop) :
    (∃ dec : R → M → P, ∀ w, ok w (dec (r w) (enc (q w)))) ↔
    ∀ b c, ∃ a, ∀ w, r w = b → enc (q w) = c → ok w a := by
  constructor
  · rintro ⟨dec,h⟩ b c
    refine ⟨dec b c, ?_⟩
    intro w h1 h2
    simpa [h1,h2] using h w
  · intro h
    classical
    refine ⟨fun b c => Classical.choose (h b c), ?_⟩
    intro w
    exact Classical.choose_spec (h (r w) (enc (q w))) w rfl rfl

theorem bounded_obstruction {Q P : Type} [Fintype P] [DecidableEq Q]
    (available : Q → Prop) (ok : Q → P → Prop)
    (bad : ∀ a, ∃ q, available q ∧ ¬ ok q a) :
    ∃ s : Finset Q, s.card ≤ Fintype.card P ∧
      (∀ q ∈ s, available q) ∧ (∀ a, ∃ q ∈ s, ¬ ok q a) := by
  classical
  choose f hf using bad
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro q hq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    exact (hf a).1
  · intro a
    exact ⟨f a,Finset.mem_image_of_mem _ (Finset.mem_univ a),(hf a).2⟩

theorem pairs_work : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
theorem triple_fails : ¬ ∃ c : Fin 3, ∀ q : Fin 3, c ≠ q := by
  rintro ⟨c,h⟩
  exact h c rfl

#print axioms protocol_iff
#print axioms bounded_obstruction
#print axioms pairs_work
#print axioms triple_fails
end PortChoices
