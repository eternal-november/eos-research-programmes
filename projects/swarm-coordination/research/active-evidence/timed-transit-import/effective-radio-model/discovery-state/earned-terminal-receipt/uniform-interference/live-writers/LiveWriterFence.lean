import Mathlib

namespace LiveWriterFence

structure Writer where
  admissible : Bool
  controlled : Bool

def step (n : Nat) (w : Writer) : Nat :=
  if w.admissible && (!w.controlled || n == 0) then n+1 else n

def run (n : Nat) (ws : List Writer) : Nat := ws.foldl step n

theorem current_fence_keeps_one (ws : List Writer)
    (covered : ∀ w ∈ ws, w.controlled = true) :
    run 1 ws = 1 := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.controlled = true := covered x (by simp)
    have hxs : ∀ w ∈ xs, w.controlled = true := by
      intro w hw
      exact covered w (by simp [hw])
    have hr : step 1 x = 1 := by simp [step, hx]
    rw [show run 1 (x :: xs) = run (step 1 x) xs from rfl, hr]
    exact ih hxs

theorem uncontrolled_second_doubles :
    run 0 [⟨true,true⟩,⟨true,false⟩] = 2 := by decide

theorem stale_unsettled_estimate_allows_both :
    step 0 ⟨true,true⟩ + step 0 ⟨true,true⟩ = 2 := by decide

#print axioms current_fence_keeps_one
#print axioms uncontrolled_second_doubles
#print axioms stale_unsettled_estimate_allows_both
end LiveWriterFence
