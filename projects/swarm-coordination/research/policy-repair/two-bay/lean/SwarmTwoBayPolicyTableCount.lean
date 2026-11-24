import SwarmTwoBayPolicyNormalForm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin

namespace SwarmTwoBay

noncomputable instance layoutsFintype (n : Nat) : Fintype (Layouts n) :=
  Fintype.ofEquiv _ (tailLayoutEquiv n)

theorem card_layouts (n : Nat) : Fintype.card (Layouts n) = 2 ^ n := by
  rw [← Fintype.card_congr (tailLayoutEquiv n), Fintype.card_fun]
  simp

/-- Any injective fixed-width binary code for this family has at least n bits. -/
theorem layout_bits_lower_bound {n bits : Nat} (code : Layouts n → Fin bits → Bool)
    (hc : Function.Injective code) : n ≤ bits := by
  have h := Fintype.card_le_of_injective code hc
  rw [card_layouts, Fintype.card_fun] at h
  simp only [Fintype.card_fin, Fintype.card_bool] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

/-- An exact decoder for every fixed B table makes the code injective. -/
theorem layout_bits_lower_bound_of_membership {n bits : Nat}
    (code : Layouts n → Fin bits → Bool)
    (accept : (Fin bits → Bool) → (Fin (n + 1) → Bool) → Prop)
    (correct : ∀ layout table, accept (code layout) table ↔ table ∈ layout.val) :
    n ≤ bits := by
  apply layout_bits_lower_bound code
  intro l r e
  apply Subtype.ext
  ext t
  rw [← correct l t, e, correct r t]

/-- At width n the normalized tail is an exact code, with decoding back to
the full table-membership relation. -/
theorem normalized_tail_exact_codec (n : Nat) :
    ∃ code : Layouts n → Fin n → Bool,
      ∃ accept : (Fin n → Bool) → (Fin (n + 1) → Bool) → Prop,
        ∀ layout table, accept (code layout) table ↔ table ∈ layout.val := by
  refine ⟨(tailLayoutEquiv n).symm, fun t b => b ∈ (tailLayoutEquiv n t).val, ?_⟩
  intro layout table
  change table ∈ ((tailLayoutEquiv n) ((tailLayoutEquiv n).symm layout)).val ↔ table ∈ layout.val
  rw [Equiv.apply_symm_apply]

#print axioms card_layouts
#print axioms layout_bits_lower_bound
#print axioms layout_bits_lower_bound_of_membership
#print axioms normalized_tail_exact_codec
end SwarmTwoBay
