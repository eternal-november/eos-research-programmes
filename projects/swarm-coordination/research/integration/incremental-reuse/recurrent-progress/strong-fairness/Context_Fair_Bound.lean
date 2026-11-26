import Mathlib

namespace ContextFairBound

theorem same_rank_avoiding_is_query {ι : Type} [DecidableEq ι]
    {a key : Finset ι} (hcard : a.card = key.card) (havoid : a ⊆ key) :
    a = key :=
  Finset.eq_of_subset_of_card_le havoid hcard.ge

theorem distinguishing_reads_injective {ι C : Type}
    (enc : (ι → Bool) → C) (read : C → ι → Bool)
    (exactly : ∀ s i, read (enc s) i = s i) :
    Function.Injective enc := by
  intro a b h
  funext i
  rw [← exactly a i, ← exactly b i, h]

theorem bit_lower_bound {ι : Type} [Fintype ι] (b : ℕ)
    (enc : (ι → Bool) → Fin (2^b)) (read : Fin (2^b) → ι → Bool)
    (exactly : ∀ s i, read (enc s) i = s i) :
    Fintype.card ι ≤ b := by
  classical
  have h := Fintype.card_le_of_injective enc (distinguishing_reads_injective enc read exactly)
  have h' : 2^Fintype.card ι ≤ 2^b := by simpa using h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h'

#print axioms same_rank_avoiding_is_query
#print axioms distinguishing_reads_injective
#print axioms bit_lower_bound
end ContextFairBound
