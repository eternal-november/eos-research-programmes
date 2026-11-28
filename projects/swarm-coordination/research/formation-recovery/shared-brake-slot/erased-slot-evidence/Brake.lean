import Mathlib

namespace SharedBrake

def runTail : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, w, r => (w,r)
  | n+1, w, r => runTail n (w-1) (r+2*w-1)

theorem signed_area_invariant (n : ℕ) (w r : ℤ) :
    (runTail n w r).2 + (runTail n w r).1 ^ 2 = r+w^2 := by
  induction n generalizing w r with
  | zero => rfl
  | succ n ih =>
    change (runTail n (w-1) (r+2*w-1)).2 +
      (runTail n (w-1) (r+2*w-1)).1 ^2 = r+w^2
    rw [ih]
    ring

theorem tail_velocity (n : ℕ) (w r : ℤ) :
    (runTail n w r).1 = w - (n : ℤ) := by
  induction n generalizing w r with
  | zero => simp [runTail]
  | succ n ih =>
    change (runTail n (w-1) (r+2*w-1)).1 = w - ((n+1 : ℕ) : ℤ)
    rw [ih]
    push_cast
    ring

theorem erased_tail (n : ℕ) (r : ℤ) :
    (runTail n (n : ℤ) (r+2*(n : ℤ))).2 =
      r + (n : ℤ)^2 + 2*(n : ℤ) := by
  have e := signed_area_invariant n (n : ℤ) (r+2*(n : ℤ))
  rw [tail_velocity] at e
  simp at e
  linarith

theorem gap_budget (d r gap : ℤ)
  (first : -gap ≤ r) (last : r+d^2+2*d ≤ gap) :
  d^2+2*d ≤ 2*gap := by linarith

theorem near_extreme_peak (v j : ℤ) (hj : 0 ≤ j) :
    v^2-v-1 ≤ v^2-2*v+2*j+(v-1) := by linarith

#print axioms erased_tail
#print axioms gap_budget
#print axioms near_extreme_peak
end SharedBrake
