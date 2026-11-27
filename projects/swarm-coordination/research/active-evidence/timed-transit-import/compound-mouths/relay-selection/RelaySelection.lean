import Mathlib

namespace CompoundCaveRelay

def select (direct via : ℕ × ℕ) : ℕ × ℕ :=
  if via.1 < direct.1 then via else direct

def viable (link : ℕ × ℕ) (r2 : ℕ) : Prop :=
  link.1 ≤ 10 ∧ link.2 ≤ r2

theorem jointFlip (r2 : ℕ) :
    (viable (10, 5000) r2 ∧ ¬ viable (13, 8125) r2 ∧
      ¬ viable (select (10, 5000) (9, 5625)) r2 ∧
      viable (select (13, 8125) (9, 3125)) r2)
      ↔ 5000 ≤ r2 ∧ r2 < 5625 := by
  simp [viable, select]
  omega

theorem safeSiteKeepsBoth (r2 : ℕ) (h : 5000 ≤ r2) :
    select (10, 5000) (10, 10000) = (10, 5000) ∧
    viable (select (10, 5000) (10, 10000)) r2 ∧
    viable (select (13, 8125) (10, 5000)) r2 := by
  simp [viable, select, h]

theorem serialTiming (a b k : ℕ) :
    (viable (if k ≤ a then (9, 5625) else (10, 5000)) 5184 ∧
      viable (if k ≤ b then (9, 3125) else (13, 8125)) 5184)
      ↔ a < k ∧ k ≤ b := by
  unfold viable
  split_ifs <;> omega

theorem someSafeActivation (a b : ℕ) :
    (∃ k, a < k ∧ k ≤ b) ↔ a < b := by
  constructor
  · rintro ⟨k, h1, h2⟩
    omega
  · intro h
    exact ⟨b, h, Nat.le_refl b⟩

#print axioms jointFlip
#print axioms safeSiteKeepsBoth
#print axioms serialTiming
#print axioms someSafeActivation
end CompoundCaveRelay
