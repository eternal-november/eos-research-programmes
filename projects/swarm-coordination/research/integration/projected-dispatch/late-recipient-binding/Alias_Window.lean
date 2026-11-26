import Mathlib

namespace AliasWindow

def Unsafe (limit old new : ℕ) (aliasTx : Bool) (aliasRx : Bool) (age : ℕ) : Prop :=
  (aliasTx = true ∨ aliasRx = true) ∧ age ≤ 4 ∧ limit < old+new

theorem exact_active_row (limit old new age : ℕ) (shared : Bool)
    (h : old ≤ limit) :
    old + (if shared = true ∧ age ≤ 4 then new else 0) ≤ limit ↔
    ¬ (shared = true ∧ age ≤ 4 ∧ limit < old+new) := by
  by_cases hc : shared = true ∧ age ≤ 4
  · rw [ite_eq_left hc]
    simp [hc.1, hc.2]
  · rw [ite_eq_right hc]
    have hr : ¬ (shared = true ∧ age ≤ 4 ∧ limit < old+new) :=
      fun z => hc ⟨z.1,z.2.1⟩
    simp [h,hr]

theorem marginal_sound (S : Set (Bool × ℕ)) (cap a b : ℕ) (tx : Bool)
    (safe : ∀ u ∈ Prod.fst '' S, ∀ t ∈ Prod.snd '' S, ¬ Unsafe cap a b tx u t) :
    ∀ w ∈ S, ¬ Unsafe cap a b tx w.1 w.2 := by
  intro w hw
  exact safe w.1 ⟨w,hw,rfl⟩ w.2 ⟨w,hw,rfl⟩

theorem diagonal_only :
    (∀ w ∈ ({(false,3),(true,5)} : Set (Bool × ℕ)), ¬ Unsafe 5 3 3 false w.1 w.2) ∧
    Unsafe 5 3 3 false true 3 ∧ Unsafe 5 3 3 false true 4 := by
  constructor
  · intro w hw
    rcases hw with h|h
    · simp [h,Unsafe]
    · have he : w=(true,5) := h
      simp [he,Unsafe]
  · norm_num [Unsafe]

#print axioms exact_active_row
#print axioms marginal_sound
#print axioms diagonal_only
end AliasWindow
