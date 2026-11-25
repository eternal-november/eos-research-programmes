import Mathlib

namespace SwarmDeadlineProfile

def early (expiry gap : ℕ → ℤ) (prev : ℤ) : ℕ → ℤ
  | 0 => max 0 (max (expiry 0) (prev + gap 0))
  | k + 1 => max 0 (max (expiry (k+1)) (early expiry gap prev k + gap (k+1)))

def admissible (e d t : ℕ → ℤ) (b : ℤ) (n : ℕ) : Prop :=
  (∀ i < n, 0 ≤ t i ∧ e i ≤ t i) ∧
  (0 < n → b + d 0 ≤ t 0) ∧
  (∀ i, i+1 < n → t i + d (i+1) ≤ t (i+1))

theorem earliest_le {e d t : ℕ → ℤ} {b : ℤ} {n : ℕ}
    (ok : admissible e d t b n) : ∀ i < n, early e d b i ≤ t i := by
  intro i
  induction i with
  | zero =>
    intro h0
    exact max_le (ok.1 0 h0).1 (max_le (ok.1 0 h0).2 (ok.2.1 h0))
  | succ j ih =>
    intro hj
    apply max_le (ok.1 (j+1) hj).1
    refine max_le (ok.1 (j+1) hj).2 ?_
    have hn : j < n := by omega
    exact le_trans (add_le_add_left (ih hn) _) (ok.2.2 j hj)

theorem earliest_contains_physical_bound (e d : ℕ → ℤ) (b : ℤ) :
    b + d 0 ≤ early e d b 0 := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem exact_earliest_profile {e d t : ℕ → ℤ} {b : ℤ} {n : ℕ} :
    admissible e d t b n ↔
      (∀ i < n, early e d b i ≤ t i) ∧
      (∀ i, i+1 < n → t i + d (i+1) ≤ t (i+1)) := by
  constructor
  · intro ok
    exact ⟨earliest_le ok,ok.2.2⟩
  · intro h
    refine ⟨?_, ?_, h.2⟩
    · intro i hi
      have hz : 0 ≤ early e d b i := by
        cases i <;> exact le_max_left _ _
      have he : e i ≤ early e d b i := by
        cases i <;> exact le_trans (le_max_left _ _) (le_max_right _ _)
      exact ⟨le_trans hz (h.1 i hi),le_trans he (h.1 i hi)⟩
    · intro hn
      exact le_trans (earliest_contains_physical_bound e d b) (h.1 0 hn)

theorem clipped_bound_iff {x t h : ℤ} (ht : t < h) :
    min x h ≤ t ↔ x ≤ t := by
  omega

#print axioms earliest_le
#print axioms earliest_contains_physical_bound
#print axioms exact_earliest_profile
#print axioms clipped_bound_iff
end SwarmDeadlineProfile
