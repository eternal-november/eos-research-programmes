import Mathlib

namespace LiftEffectWindow

theorem conflict_at_issue (q e f l r : ℤ) (hd : e ≤ f) (hr : l ≤ r) :
    (∃ d : ℤ, e ≤ d ∧ d ≤ f ∧ l ≤ q + d ∧ q + d ≤ r) ↔
      l - f ≤ q ∧ q ≤ r - e := by
  constructor
  · rintro ⟨d, hd0, hd1, hl, hR⟩
    omega
  · rintro ⟨hl, hR⟩
    refine ⟨max e (l - q), ?_, ?_, ?_, ?_⟩
    · exact le_max_left _ _
    · exact max_le_iff.mpr ⟨hd, by omega⟩
    · have h := le_max_right e (l - q)
      omega
    · have h : max e (l - q) ≤ r - q := max_le_iff.mpr ⟨by omega, by omega⟩
      omega

theorem common_history_authority {B P : Type}
    (may : B → P → ℤ → Prop) (permit : B → P → ℤ → Prop)
    (earliest latest : B → ℤ) (q : ℤ) :
    (∀ b p d, earliest b ≤ d → d ≤ latest b →
      may b p (q+d) → permit b p (q+d)) ↔
      ¬(∃ b p d, earliest b ≤ d ∧ d ≤ latest b ∧
        may b p (q+d) ∧ ¬permit b p (q+d)) := by
  constructor
  · intro h hex
    rcases hex with ⟨b,p,d,he,hl,hm,hp⟩
    exact hp (h b p d he hl hm)
  · intro h b p d he hl hm
    by_contra! hp
    exact h ⟨b,p,d,he,hl,hm,hp⟩

end LiftEffectWindow

#print axioms LiftEffectWindow.conflict_at_issue
#print axioms LiftEffectWindow.common_history_authority
