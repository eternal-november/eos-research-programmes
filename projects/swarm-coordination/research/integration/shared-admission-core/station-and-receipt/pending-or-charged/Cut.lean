import Mathlib

namespace QueueEffect

-- Q has no other traffic; the optional probe costs 60 and the old report 173.
-- A queued probe can be removed, but an already charged probe cannot.
def viable (cap live : Nat) (keepPending : Bool) : Prop :=
  live + (if keepPending then 60 else 0) + 173 ≤ cap

theorem qualified_cut (cap : Nat) (base : 173 ≤ cap) (tight : cap < 233) :
    viable cap 0 false ∧ ¬ viable cap 0 true ∧ ¬ viable cap 60 false := by
  simp [viable]
  omega

theorem headroom_cut (cap : Nat) :
    (viable cap 0 true ↔ 233 ≤ cap) ∧ (viable cap 60 false ↔ 233 ≤ cap) := by
  simp [viable]

-- A pure removal decision on a shared observation cannot certify use of
-- Q under both histories; even removal does not change the settled debit.
theorem no_shared_primary (cap : Nat) (tight : cap < 233) :
    ¬ ∃ keep : Bool, viable cap 0 keep ∧ viable cap 60 false := by
  rintro ⟨keep, _, h⟩
  simp [viable] at h
  omega

#print axioms qualified_cut
#print axioms headroom_cut
#print axioms no_shared_primary
end QueueEffect
