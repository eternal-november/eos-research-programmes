import Mathlib

namespace SwarmReceiptEpoch

def colours (L : ℕ) : ℕ := L / 2 + 1

def signer (g : ℕ) : ℕ := g % 2

def tag (L g : ℕ) : ℕ := (g / 2) % colours L

theorem tag_in_range (L g : ℕ) : tag L g < colours L := by
  apply Nat.mod_lt
  unfold colours
  omega

theorem colour_separates (L g h : ℕ) (hh : h ≤ g) (ha : g - h ≤ L)
    (hs : signer g = signer h) (ht : tag L g = tag L h) : g = h := by
  unfold signer at hs
  unfold tag at ht
  by_contra hn
  have hb : h / 2 < g / 2 := by omega
  have hp := Nat.mod_add_div (g / 2) (colours L)
  have hq := Nat.mod_add_div (h / 2) (colours L)
  have hd : (h / 2) / colours L < (g / 2) / colours L := by
    by_contra hnq
    have hm := Nat.mul_le_mul_left (colours L) (show (g / 2) / colours L ≤ (h / 2) / colours L by omega)
    omega
  have hm := Nat.mul_le_mul_left (colours L) (show (h / 2) / colours L + 1 ≤ (g / 2) / colours L by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  unfold colours at *
  omega

theorem any_exact_alternating_tag_needs_enough_colours (L m : ℕ) (decode : ℕ → Fin m)
    (dist : ∀ g h, h < g → g - h ≤ L → signer g = signer h → decode g ≠ decode h) :
    colours L ≤ m := by
  classical
  let f : Fin (colours L) → Fin m := fun i => decode (2 * (i : ℕ))
  have inj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    by_contra hn
    have hi := i.isLt
    have hj := j.isLt
    unfold colours at hi hj
    change decode (2 * (i : ℕ)) = decode (2 * (j : ℕ)) at he
    rcases Nat.lt_or_gt_of_ne hn with h | h
    · exact dist _ _ (by omega) (by omega) (by unfold signer; omega) he.symm
    · exact dist _ _ (by omega) (by omega) (by unfold signer; omega) he
  simpa using Fintype.card_le_of_injective f inj

#print axioms tag_in_range
#print axioms colour_separates
#print axioms any_exact_alternating_tag_needs_enough_colours
end SwarmReceiptEpoch
