import Mathlib
namespace GuardedAppend

theorem headroom_migration (cap live pending emitted report : Nat)
    (h : live + (emitted + pending) + report ≤ cap) :
    (live + emitted) + pending + report ≤ cap := by omega

theorem future_attempt_bound (liveKept live report cap : Nat)
    (observed actual suffix : List Nat)
    (hl : liveKept ≤ live) (hp : actual.sum ≤ observed.sum)
    (h : live + observed.sum + report ≤ cap) :
    liveKept + (((actual ++ [report]) ++ suffix).take (actual.length + 1)).sum ≤ cap := by
  rw [show actual.length + 1 = (actual ++ [report]).length by simp]
  simp only [List.take_left, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  omega

theorem double_fanout_boundary (cap : Nat) (lo : 233 ≤ cap) (hi : cap < 293) :
    60 + 173 ≤ cap ∧ ¬ 60 + 60 + 173 ≤ cap := by omega

#print axioms headroom_migration
#print axioms future_attempt_bound
#print axioms double_fanout_boundary
end GuardedAppend
