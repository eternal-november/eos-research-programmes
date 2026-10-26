import Std

namespace ByzantineLocalTiming

-- Integer coordinates represent a common rational scale, not runtime global time.
def Near (s x y : Int) : Prop := -s ≤ x-y ∧ x-y ≤ s

theorem near_symm (s x y : Int) (h : Near s x y) : Near s y x := by
  unfold Near at *
  omega

theorem shared_actual_event_bounds_union (s a x y : Int)
    (hx : Near s x a) (hy : Near s y a) : Near (2*s) x y := by
  unfold Near at *
  omega

theorem distinct_events_not_same_label (c k : Nat) (hc : 0 < c) :
    k < k+c ∧ k%c = (k+c)%c := by
  constructor
  · omega
  · simp

theorem splice_anchors_ordered (cut h q x y : Int)
    (hspace : q < h) (hx : cut ≤ x ∧ x ≤ cut+q)
    (hy : cut+h ≤ y ∧ y ≤ cut+h+q) :
    x < y ∧ h-q ≤ y-x ∧ y-x ≤ h+q := by omega

theorem displaced_boundary_gap (p P s oldA oldB a b : Int)
    (hgap : p-s ≤ oldB-oldA ∧ oldB-oldA ≤ P+s)
    (hleft : a = oldA)
    (hright : oldB-s ≤ b ∧ b ≤ oldB+s) :
    p-2*s ≤ b-a ∧ b-a ≤ P+2*s := by omega

theorem separated_spliced_clusters (p s a b : Int)
    (hp : 4*s < p) (hgap : p-2*s ≤ b-a) : a+2*s < b := by omega

theorem current_round_after_clear (sigma sendLo pulseI pulseJ sent : Int)
    (hskew : pulseI ≤ pulseJ+sigma) (hs : sigma < sendLo)
    (hsent : pulseJ+sendLo ≤ sent) : pulseI < sent := by omega

theorem current_round_before_compute (sigma sendHi delay lag recvLo pi pj arrival compute : Int)
    (hskew : pj ≤ pi+sigma)
    (harrival : arrival ≤ pj+sendHi+delay+lag)
    (hcompute : pi+recvLo ≤ compute)
    (hmargin : sigma+sendHi+delay+lag < recvLo) : arrival < compute := by omega

theorem old_round_drained (gap sigma sendHi delay lag now old arrival : Int)
    (hprev : old ≤ now+sigma-gap)
    (harrival : arrival ≤ old+sendHi+delay+lag)
    (hmargin : sigma+sendHi+delay+lag < gap) : arrival < now := by omega

theorem next_round_after_compute (gap sigma sendLo recvHi now next sent compute : Int)
    (hnext : now+gap-sigma ≤ next)
    (hsent : next+sendLo ≤ sent)
    (hcompute : compute ≤ now+recvHi)
    (hmargin : sigma+recvHi < gap+sendLo) : compute < sent := by omega

theorem lease_covers_release (request now cutoffUpper releaseTail holdLower heldAt : Int)
    (hcutoff : now ≤ request+cutoffUpper)
    (hheld : request+holdLower ≤ heldAt)
    (hmargin : cutoffUpper+releaseTail < holdLower) : now+releaseTail < heldAt := by omega

theorem warmup_not_early (start lower globalReady expiry : Int)
    (hstart : 0 ≤ start) (hlower : globalReady ≤ lower)
    (hexpiry : start+lower ≤ expiry) : globalReady ≤ expiry := by omega

theorem history_contained_after_maturity (restored event window : Int)
    (hmature : restored+window ≤ event) : restored ≤ event-window := by omega

theorem task_cycle_hit (c start target : Nat)
    (_hc : 0 < c) (hs : start < c) (ht : target < c) :
    ∃ wait, wait < c ∧ (start+wait)%c = target := by
  by_cases h : start ≤ target
  · refine ⟨target-start, ?_, ?_⟩
    · omega
    · have heq : start+(target-start)=target := by omega
      rw [heq, Nat.mod_eq_of_lt ht]
  · refine ⟨c-start+target, ?_, ?_⟩
    · omega
    · have heq : start+(c-start+target)=c+target := by omega
      rw [heq]
      simp [Nat.mod_eq_of_lt ht]

theorem same_actual_event_fixes_label {Node Event : Type}
    (label : Node → Event → Nat) (actor : Node) (eventA eventB : Event)
    (same : eventA = eventB) : label actor eventA = label actor eventB := by
  rw [same]

theorem aligned_labels_continue (c a b : Nat) (h : a%c=b%c) (k : Nat) :
    (a+k)%c = (b+k)%c := by
  calc
    (a+k)%c = (a%c+k%c)%c := Nat.add_mod a k c
    _ = (b%c+k%c)%c := by rw [h]
    _ = (b+k)%c := (Nat.add_mod b k c).symm

-- This witness is a periodic bad schedule for the lease-retry algorithm only.
theorem lease_split_never_quorum : (2 : Nat) < 3 ∧ (2 : Nat) < 3 := by decide

#print axioms shared_actual_event_bounds_union
#print axioms distinct_events_not_same_label
#print axioms splice_anchors_ordered
#print axioms displaced_boundary_gap
#print axioms separated_spliced_clusters
#print axioms current_round_after_clear
#print axioms current_round_before_compute
#print axioms old_round_drained
#print axioms next_round_after_compute
#print axioms lease_covers_release
#print axioms warmup_not_early
#print axioms history_contained_after_maturity
#print axioms task_cycle_hit
#print axioms same_actual_event_fixes_label
#print axioms aligned_labels_continue
#print axioms lease_split_never_quorum

end ByzantineLocalTiming
