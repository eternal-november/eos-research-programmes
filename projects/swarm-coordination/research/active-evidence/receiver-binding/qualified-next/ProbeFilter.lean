import Mathlib

def seen (shared dropped : Bool) : Bool := !shared && !dropped

def afterOld (shared dropped : Bool) : ℕ :=
  (if shared then 2 else if dropped then 0 else 1) + 2

def nextFits (shared dropped : Bool) (z : ℕ) : Prop :=
  afterOld shared dropped + z ≤ 5

theorem observed_positive (shared dropped : Bool)
    (h : seen shared dropped = true) :
    shared = false ∧ dropped = false := by
  cases shared <;> cases dropped <;> simp_all [seen]

theorem complete_absence (shared : Bool)
    (h : seen shared false = false) :
    shared = true := by
  cases shared <;> simp_all [seen]

theorem uncertain_absence_two_witnesses :
    seen true false = false ∧ seen false true = false ∧
    ¬ nextFits true false 2 ∧ nextFits false true 2 := by norm_num [seen, nextFits, afterOld]

theorem informative_is_not_free :
    seen false false = true ∧ seen false true = false ∧
    ¬ nextFits false false 3 ∧ nextFits false true 3 := by norm_num [seen, nextFits, afterOld]

#print axioms observed_positive
#print axioms complete_absence
#print axioms uncertain_absence_two_witnesses
#print axioms informative_is_not_free
