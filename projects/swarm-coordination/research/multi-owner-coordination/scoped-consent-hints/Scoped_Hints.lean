import Mathlib

namespace ScopedHints

/-- The admissible charter can serve every bay at capacity c iff every set
    of bays can fit among the response positions of its permitted hints. -/
theorem slots_hall {Bay Hint : Type} [DecidableEq Hint]
    (H : Bay → Finset Hint) (c : ℕ) :
    (∀ U : Finset Bay, U.card ≤ (U.biUnion H).card*c) ↔
      ∃ f : Bay → Hint × Fin c, Function.Injective f ∧ ∀ j, (f j).1 ∈ H j := by
  classical
  let slots := fun j => (H j).product (Finset.univ : Finset (Fin c))
  have hUnion (U : Finset Bay) : U.biUnion slots =
      (U.biUnion H).product (Finset.univ : Finset (Fin c)) := by
    ext ij
    simp [slots]
  have hh (U : Finset Bay) : (U.biUnion slots).card = (U.biUnion H).card*c := by
    rw [hUnion]
    change ((U.biUnion H) ×ˢ (Finset.univ : Finset (Fin c))).card = _
    simp [Finset.card_product]
  have hm (j : Bay) (z : Hint × Fin c) : z ∈ slots j ↔ z.1 ∈ H j := by simp [slots]
  have main := Finset.all_card_le_biUnion_card_iff_exists_injective slots
  simp only [hh, hm] at main
  exact main

theorem local_bits_injective {β Message : Type}
    (enc : (β → Bool) → Message) (dec : Message → β → Bool)
    (qualified : ∀ x j, dec (enc x) j = x j) :
    Function.Injective enc := by
  intro x y hs
  funext j
  rw [← qualified x j, ← qualified y j, hs]

#print axioms slots_hall
#print axioms local_bits_injective
end ScopedHints
