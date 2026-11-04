import Std

/-! Incident-token projection kernels for RECEIVER.md. These do not establish
    the physical graph, raw supply, or history-return premises. -/
namespace ByzantineReceiver

def projected {E S : Type} (events : List E) (slot : E → Option S) : List S :=
  events.filterMap slot

theorem projection_length {E S : Type} (events : List E) (slot : E → Option S) :
    (projected events slot).length ≤ events.length := by
  exact List.length_filterMap_le slot events

theorem projection_covers {E S : Type} (events : List E) (slot : E → Option S)
    (affected : S → Prop)
    (actualReach : ∀ s, affected s → ∃ e, e ∈ events ∧ slot e = some s) :
    ∀ s, affected s → s ∈ projected events slot := by
  intro s hs
  exact List.mem_filterMap.mpr (actualReach s hs)

theorem same_cover_two_consumers {E H S : Type} (events : List E)
    (hosts : E → Option H) (slots : E → Option S) (bound : Nat)
    (rawBound : events.length ≤ bound) :
    (projected events hosts).length ≤ bound ∧
    (projected events slots).length ≤ bound := by
  exact ⟨Nat.le_trans (projection_length events hosts) rawBound,
         Nat.le_trans (projection_length events slots) rawBound⟩

theorem projection_preserves_append {E S : Type} (past fresh : List E)
    (slot : E → Option S) :
    projected (past ++ fresh) slot = projected past slot ++ projected fresh slot := by
  exact List.filterMap_append

theorem owner_collapse_loses_two_sites :
    ([0, 0] : List Nat).eraseDups.length = 1 ∧
    ([1, 2] : List Nat).eraseDups.length = 2 := by decide

theorem negative_private_threshold_rejects (raw threshold : Int)
    (rawUnsigned : 0 ≤ raw) (privateNegative : threshold < 0) :
    ¬ raw ≤ threshold := by omega

theorem private_and_raw_allocations :
    20362 + 8*(2*40+1) ≤ (32768 : Nat) ∧
    2*80*(3*40)*256 ≤ (2048-976)*(2*26*(27283+40)) := by decide

#print axioms projection_length
#print axioms projection_covers
#print axioms same_cover_two_consumers
#print axioms projection_preserves_append
#print axioms owner_collapse_loses_two_sites
#print axioms negative_private_threshold_rejects
#print axioms private_and_raw_allocations
end ByzantineReceiver
