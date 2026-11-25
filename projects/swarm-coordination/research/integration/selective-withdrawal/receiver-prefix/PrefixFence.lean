import Std

def advance (floor : Nat) (p : Nat) (msg : Nat × Nat) : Nat :=
  if floor ≤ msg.1 then max p msg.2 else p

theorem sealed_prefix (floor : Nat) (p : Nat) (late : List (Nat × Nat))
    (old : ∀ m ∈ late, m.1 < floor) :
    late.foldl (advance floor) p = p := by
  induction late generalizing p with
  | nil => rfl
  | cons m l ih =>
    have hm : ¬ floor ≤ m.1 := Nat.not_le_of_gt (old m (by simp))
    have hl : ∀ u ∈ l, u.1 < floor := by
      intro u hu
      exact old u (List.mem_cons_of_mem m hu)
    simpa [List.foldl_cons, advance, hm] using ih p hl

theorem no_old_conflict (floor p j k : Nat) (late : List (Nat × Nat))
    (old : ∀ m ∈ late, m.1 < floor) (below : p < j) (conflict : j ≤ k) :
    k > late.foldl (advance floor) p := by
  rw [sealed_prefix floor p late old]
  exact Nat.lt_of_lt_of_le below conflict

theorem serial_admission (ack clear grant dur deadline : Nat) :
    (∃ t, ack ≤ t ∧ clear ≤ t ∧ grant ≤ t ∧ t + dur ≤ deadline) ↔
      max (max ack clear) grant + dur ≤ deadline := by
  constructor
  · rintro ⟨t, a, c, g, d⟩
    exact Nat.le_trans (Nat.add_le_add_right (max_le (max_le a c) g) _) d
  · intro h
    exact ⟨max (max ack clear) grant, by omega, by omega, by omega, h⟩

#print axioms sealed_prefix
#print axioms no_old_conflict
#print axioms serial_admission
