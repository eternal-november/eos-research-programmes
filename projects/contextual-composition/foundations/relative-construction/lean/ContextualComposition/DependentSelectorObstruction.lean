module

public import ContextualComposition.FiniteWriterObstruction

/-! Fair-bit erasure and variable continuation selection in the native family-completion example. Each continuation has a singleton witness; the source preserves its first raw bit. -/

@[expose] public section
namespace ContextualComposition.DependentSelectorObstruction

open FiniteWriterObstruction

def erase : Bool → Unit := fun _ => ()
def select (w : Bool) := w
def sourceOutput (w : Bool × Unit) := select w.1
def targetOutput (j : Bool) (_ : Unit × Unit) := j

/-- For a fixed offered component its singleton raw witness and returned index are the same after erasure. -/
theorem fixed_continuation (j : Bool) (w : Bool) (x : Unit) :
    (fun _ : Bool × Unit => j) (w,x) = targetOutput j (erase w,x) := rfl

theorem erasure_preserves : fair.comp (dirac (A := .bit) (B := .one) erase) = dirac (fun _ => ()) :=
  unique_terminal _

/-- No target component's body square commutes, even allowing an arbitrary comparison on the entire retained raw input. -/
theorem no_body_square : ¬ ∃ (j : Bool) (r : Bool × Unit → Unit × Unit), ∀ z, sourceOutput z = targetOutput j (r z) := by
  rintro ⟨j,r,h⟩
  exact Bool.noConfusion ((h ⟨false,()⟩).trans (h ⟨true,()⟩).symm)

theorem source_law : fair.comp (dirac (A := .bit) (B := .bit) select) = fair := by
  apply Kernel.ext; intro a b
  change (∑ i : Bool, (1 : ℝ)/2 * (if select i = b then 1 else 0)) = 1/2
  cases b <;> simp [select]

theorem different_output_laws (j : Bool) :
    fair.comp (dirac (A := .bit) (B := .bit) select) ≠ dirac (A := .one) (B := .bit) (fun _ => j) := by
  rw [source_law]
  intro eq
  have h := congrArg (fun q : Kernel .one .bit => q.mass () (!j)) eq
  have hj : j ≠ !j := by cases j <;> decide
  change (1 : ℝ) / 2 = if j = !j then 1 else 0 at h
  simp only [hj, ite_false] at h
  exact (div_ne_zero one_ne_zero (by exact two_ne_zero)) h

end ContextualComposition.DependentSelectorObstruction
