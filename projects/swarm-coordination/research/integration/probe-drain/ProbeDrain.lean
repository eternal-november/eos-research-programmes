import Mathlib

/-- Packing is stated in terms of already justified per-slot capacity. -/
theorem window_capacity (n c H q : ℕ) (h : q ≤ H)
    (checked : n ≤ c * (H - q)) :
    n + c * q ≤ c * H := by
  have aux : c * (H - q) + c * q = c * H := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  omega

theorem upgrade_exact (n cap u : ℕ) (h : u ≤ n) :
    n - u ≤ cap ↔ n - cap ≤ u := by
  omega

def quietAge (trace : List Bool) (age : ℕ) : ℕ :=
  trace.foldl (fun a probe => if probe then 0 else a + 1) age

/-- A reset followed by one quiet slot returns to the same degraded age. -/
theorem two_slot_loop (k : ℕ) :
    quietAge ((List.replicate k [true, false]).flatten) 1 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, quietAge] at ih ⊢
    exact ih

#print axioms window_capacity
#print axioms upgrade_exact
#print axioms two_slot_loop

theorem prefix_rank (capacity rank deadline : ℕ) (p : 0 < capacity)
    (h : rank ≤ capacity * deadline) :
    (rank + capacity - 1) / capacity ≤ deadline := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul p, Nat.succ_mul, Nat.mul_comm deadline capacity]
  omega

#print axioms prefix_rank
