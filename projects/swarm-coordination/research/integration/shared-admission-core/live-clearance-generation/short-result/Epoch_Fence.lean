import Mathlib

namespace EpochFence

/-- Old minting stops at `last`; admissible delay includes its endpoint.
The new binding accepts at and after `reopen`. All bounds are on one clock. -/
def OldCouldArrive (last latency reopen : Nat) : Prop :=
  ∃ mint arrive, mint ≤ last ∧ mint ≤ arrive ∧ arrive ≤ mint + latency ∧ reopen ≤ arrive

theorem old_could_arrive_iff (last latency reopen : Nat) :
    OldCouldArrive last latency reopen ↔ reopen ≤ last + latency := by
  constructor
  · rintro ⟨mint, arrive, hm, _, ha, hr⟩
    omega
  · intro h
    exact ⟨last, last+latency, le_rfl, by omega, le_rfl, h⟩

theorem reuse_without_alias (last latency reopen : Nat) :
    ¬ OldCouldArrive last latency reopen ↔ last + latency < reopen := by
  rw [old_could_arrive_iff]
  omega

theorem inclusive_edge (last latency : Nat) :
    OldCouldArrive last latency (last + latency) ∧
      ¬ OldCouldArrive last latency (last + latency + 1) := by
  rw [old_could_arrive_iff, reuse_without_alias]
  omega

end EpochFence

#print axioms EpochFence.old_could_arrive_iff
#print axioms EpochFence.reuse_without_alias
#print axioms EpochFence.inclusive_edge
