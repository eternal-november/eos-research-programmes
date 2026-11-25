import Mathlib
namespace EffectFence

theorem first_unannounced (F s l t : Nat) :
  (F ≤ t ∧ s + l < t) ↔ max F (s+l+1) ≤ t := by
  omega

theorem safe_on_silence (F s l h : Nat) :
  (∀ t : Nat, F ≤ t → s+l < t → s+h ≤ t) ↔
  s+h ≤ max F (s+l+1) := by
  constructor
  · intro H
    exact H (max F (s+l+1)) (by omega) (by omega)
  · intro H t hf hs
    omega

theorem fallback_needed (F s l old report : Nat) :
  (∀ t : Nat, F ≤ t → t ≤ s+l → report ≤ old) ↔
  (s+l < F ∨ report ≤ old) := by
  constructor
  · intro H
    by_cases h : F ≤ s+l
    · exact Or.inr (H F (Nat.le_refl _) h)
    · exact Or.inl (by omega)
  · intro H t hf hs
    omega

theorem controlled_fence_cannot_raise_physical_floor (F f p : Nat)
  (hp : p ≤ max F f) : min (max F f) p = p := by omega

theorem safe_union_two (F G s l m h : Nat) :
  (∀ t : Nat, ((F ≤ t ∧ s+l<t) ∨ (G ≤ t ∧ s+m<t)) → s+h ≤ t) ↔
  s+h ≤ min (max F (s+l+1)) (max G (s+m+1)) := by
  constructor
  · intro H
    have hl := H (max F (s+l+1)) (Or.inl ((first_unannounced F s l _).mpr (Nat.le_refl _)))
    have hr := H (max G (s+m+1)) (Or.inr ((first_unannounced G s m _).mpr (Nat.le_refl _)))
    omega
  · intro H t ht
    rcases ht with hl | hr
    · have := (first_unannounced F s l t).mp hl
      omega
    · have := (first_unannounced G s m t).mp hr
      omega

end EffectFence
#print axioms EffectFence.first_unannounced
#print axioms EffectFence.safe_on_silence
#print axioms EffectFence.fallback_needed
#print axioms EffectFence.controlled_fence_cannot_raise_physical_floor
#print axioms EffectFence.safe_union_two
