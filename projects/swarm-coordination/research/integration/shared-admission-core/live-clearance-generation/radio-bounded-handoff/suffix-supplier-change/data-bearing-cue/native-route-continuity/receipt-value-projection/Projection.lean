namespace ReceiptCodec

structure Key where
  intent : Nat
  payload : Nat
  tick : Nat
deriving DecidableEq

abbrev Receipt := Key × Nat

def inflate (resultAt : Key → Nat) (keys : List Key) : List Receipt :=
  keys.map fun k => (k, resultAt k)

theorem restore_exact (resultAt : Key → Nat) (rows : List Receipt)
    (h : ∀ r ∈ rows, resultAt r.1 = r.2) :
    inflate resultAt (rows.map Prod.fst) = rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have head := h r (by simp)
    have rest : ∀ x ∈ rs, resultAt x.1 = x.2 := by
      intro x hx
      exact h x (by simp [hx])
    rcases r with ⟨key, value⟩
    simp [inflate] at head ⊢
    exact ⟨head, by simpa [inflate] using ih rest⟩

theorem result_agreement_necessary (resultAt : Key → Nat) (rows : List Receipt)
    (h : inflate resultAt (rows.map Prod.fst) = rows) :
    ∀ r ∈ rows, resultAt r.1 = r.2 := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    rcases r with ⟨key, value⟩
    simp [inflate] at h
    intro r hr
    rcases List.mem_cons.mp hr with eq | neq
    · subst r
      exact h.1
    · exact ih (by simpa [inflate] using h.2) r neq

theorem no_receipt_from_log (r : Key → Nat) : inflate r [] = [] := rfl
end ReceiptCodec
