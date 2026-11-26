import Mathlib

namespace RetirementSpan

theorem exact_send (x a b u v j k tail work cutoff : ℤ)
    (hst : a ≤ b) (hdr : u ≤ v) (hbr : j ≤ k)
    (hp : 0 ≤ work) (hm : work ≤ tail) :
    (∀ (s f g : ℤ), a ≤ s → s ≤ b → x+u ≤ f → f ≤ x+v →
      j ≤ g → g ≤ k →
      (s < f ∧ s+work < f+g) ∧
        (∀ t, s ≤ t → t ≤ s+tail → t < f+g → t < cutoff)) ↔
    (b+1-u ≤ x ∧ b+work+1-j-u ≤ x ∧
      (b+tail < cutoff ∨ x ≤ cutoff-v-k)) := by
  constructor
  · intro H
    have h0 := H b (x+u) j hst le_rfl le_rfl (by omega) le_rfl hbr
    refine ⟨by omega, by omega, ?_⟩
    by_cases hn : b+tail < cutoff
    · exact Or.inl hn
    · right
      have h1 := H b (x+v) k hst le_rfl (by omega) le_rfl hbr le_rfl
      by_contra! hh
      have hneg := h1.2 (max b cutoff) (le_max_left _ _) (by omega) (by omega)
      omega
  · rintro ⟨h1,h2,h3⟩ s f g hs1 hs2 hf1 hf2 hg1 hg2
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro t ht1 ht2 ht3
    omega

end RetirementSpan

#print axioms RetirementSpan.exact_send
