import Mathlib

namespace FrameQuotient

theorem uniform_pair {R O V : Type}
    (obs : R → O) (rot : R → V ≃ V) (w₁ w₂ : V) :
    (∀ r s, obs r = obs s →
      ∃ x y, rot r x = w₁ ∧ rot s x = w₁ ∧
             rot r y = w₂ ∧ rot s y = w₂) ↔
    (∀ r s, obs r = obs s →
      (rot r).symm w₁ = (rot s).symm w₁ ∧
      (rot r).symm w₂ = (rot s).symm w₂) := by
  constructor
  · intro H r s e
    obtain ⟨x,y,hx,hx',hy,hy'⟩ := H r s e
    refine ⟨?_,?_⟩
    · calc
        (rot r).symm w₁ = x := by rw [← hx]; exact (rot r).symm_apply_apply x
        _ = (rot s).symm w₁ := by rw [← hx']; exact ((rot s).symm_apply_apply x).symm
    · calc
        (rot r).symm w₂ = y := by rw [← hy]; exact (rot r).symm_apply_apply y
        _ = (rot s).symm w₂ := by rw [← hy']; exact ((rot s).symm_apply_apply y).symm
  · intro H r s e
    obtain ⟨hx,hy⟩ := H r s e
    refine ⟨(rot r).symm w₁, (rot r).symm w₂, ?_, ?_, ?_, ?_⟩
    · exact (rot r).apply_symm_apply w₁
    · rw [hx]; exact (rot s).apply_symm_apply w₁
    · exact (rot r).apply_symm_apply w₂
    · rw [hy]; exact (rot s).apply_symm_apply w₂

end FrameQuotient

#print axioms FrameQuotient.uniform_pair
