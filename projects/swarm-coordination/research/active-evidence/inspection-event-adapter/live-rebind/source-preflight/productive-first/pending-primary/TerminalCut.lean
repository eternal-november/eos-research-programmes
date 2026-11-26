import Lean
namespace TerminalCut

def ExactlyOnce (old alternate : Bool) : Prop :=
  (old = true ∧ alternate = false) ∨ (old = false ∧ alternate = true)

theorem pending_indistinguishable (choose : Bool → Bool) :
    ¬ (ExactlyOnce true (choose false) ∧ ExactlyOnce false (choose false)) := by
  cases h : choose false <;> simp [ExactlyOnce]

theorem guarded_replacement {old alternate : Bool}
    (noLate : old = false) (newPaid : alternate = true) :
    ExactlyOnce old alternate := Or.inr ⟨noLate,newPaid⟩

theorem retain_if_debit_excludes {base charged alternate cap : Nat}
    (overbooked : cap < base + charged + alternate) :
    ¬ (base + charged + alternate ≤ cap) := Nat.not_le_of_lt overbooked

#print axioms pending_indistinguishable
#print axioms guarded_replacement
#print axioms retain_if_debit_excludes
end TerminalCut
