import Lean

namespace Footprint

universe u v
variable {Cell : Type u} {Summary : Type v}

/-- All separately lawful named queries require retaining distinct cells. -/
theorem injective_of_exact (encode : Cell → Summary)
    (permits : Summary → Cell → Prop)
    (exactly : ∀ cell query, permits (encode cell) query ↔ cell ≠ query) :
    Function.Injective encode := by
  intro a b h
  by_contra different
  have yes := (exactly a b).mpr different
  rw [h] at yes
  exact (exactly b b).mp yes rfl

theorem one_query_scope {a b : Cell} (h : a ≠ b) :
    ¬((a ≠ a) ↔ (b ≠ a)) := by
  intro both
  exact both.mpr (Ne.symm h) rfl

#print axioms injective_of_exact
#print axioms one_query_scope
end Footprint
