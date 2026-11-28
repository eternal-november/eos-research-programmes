import Mathlib
namespace StableDock

-- a is the retry size, b the earlier Q debit, h the same-window
-- receiving debit of the transfer on the resolved destination.
def delivery (a b h c : ℕ) : Prop := b+a ≤ c ∧ h+a ≤ c

theorem exact_capacity (a b h c : ℕ) :
    delivery a b h c ↔ a+max b h ≤ c := by
  unfold delivery
  rcases le_total b h with w|w
  · rw [max_eq_right w]
    omega
  · rw [max_eq_left w]
    omega

theorem packed (a b c : ℕ) (hb : 1 ≤ b) :
    delivery a b 1 c ↔ a+b ≤ c := by
  rw [exact_capacity, max_eq_left hb]

theorem split_at_tight (a : ℕ) :
    delivery a 1 1 (a+1) ∧ ¬ delivery a 1 2 (a+1) := by
  unfold delivery
  omega

def additionalCredit (imported : Bool) := !imported
def countCredits (actual imported : Bool) : ℕ :=
  actual.toNat + (additionalCredit imported).toNat

theorem exact_once_iff_import (actual imported : Bool) :
    countCredits actual imported = 1 ↔ actual = imported := by
  cases actual <;> cases imported <;> decide

theorem no_constant_repair (imported : Bool) :
    ¬ (countCredits true imported = 1 ∧ countCredits false imported = 1) := by
  cases imported <;> decide

theorem profile_scope {K : Type} (a b : K → Bool) :
    (∀ k, countCredits (a k) (b k) = 1) ↔ a = b := by
  constructor
  · intro h
    funext k
    exact (exact_once_iff_import (a k) (b k)).mp (h k)
  · intro h k
    exact (exact_once_iff_import (a k) (b k)).mpr (congrFun h k)

end StableDock
#print axioms StableDock.exact_capacity
#print axioms StableDock.packed
#print axioms StableDock.exact_once_iff_import
#print axioms StableDock.no_constant_repair

#print axioms StableDock.profile_scope
