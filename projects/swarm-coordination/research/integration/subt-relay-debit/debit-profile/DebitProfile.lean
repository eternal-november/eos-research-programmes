import Std
def peak (l : List Nat) : Nat :=
  l.foldr Nat.max 0

theorem peak_bound (l : List Nat) (C : Nat) :
    peak l ≤ C ↔ ∀ x ∈ l, x ≤ C := by
  induction l with
  | nil => simp [peak]
  | cons a l ih =>
    change max a (peak l) ≤ C ↔ _
    simp [ih, or_imp, forall_and]

theorem robust_exact (l : List Nat) (d C : Nat) (hdl : d ≤ C) :
    peak l + d ≤ C ↔ ∀ x ∈ l, x + d ≤ C := by
  have h (x : Nat) : x + d ≤ C ↔ x ≤ C - d := by omega
  simp only [h, peak_bound]

theorem separating_probe (lo hi C : Nat) (hlt : lo < hi) (hc : hi ≤ C) :
    0 < C - lo ∧ lo + (C - lo) = C ∧ C < hi + (C - lo) := by
  omega

#print axioms peak_bound
#print axioms robust_exact
#print axioms separating_probe
