import Mathlib
namespace AuditScope
theorem widened_query_obstructed {E A : Type} (decode : E → A)
    {x y : E} {left right : A}
    (same : x = y) (different : left ≠ right) :
    ¬ (decode x = left ∧ decode y = right) := by
  rintro ⟨hx, hy⟩
  apply different
  exact hx.symm.trans ((congrArg decode same).trans hy)

def select {A : Type} (left right : A) (ordinal : Bool) : A :=
  if ordinal then right else left

theorem two_classes_one_bit {A : Type} (left right : A) :
    select left right false = left ∧ select left right true = right :=
  ⟨rfl,rfl⟩

theorem two_classes_not_zero_bits {A : Type} {left right : A}
    (different : left ≠ right) (decode : Unit → A) :
    ¬ (decode () = left ∧ decode () = right) :=
  widened_query_obstructed decode rfl different
end AuditScope
