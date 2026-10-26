import Std

/-! New arithmetic/continuation obligations for the delayed writer cutoff.
The gross stiction and stroke lemmas are retained in Operations.lean.
The continuous source proof and its remaining adapters are in CLAMP.md. -/
namespace ByzantineNoisyClamp

theorem robust_join_sound (current sampled reported error ageLoss marker : Int)
    (readUpper : reported ≤ sampled + error)
    (rateUpper : sampled ≤ current + ageLoss)
    (guard : marker ≤ reported - error - ageLoss) : marker ≤ current := by omega

theorem reset_zero_cannot_join (reported error ageLoss marker : Int)
    (positive : 0 < marker) (bound : reported ≤ error + ageLoss) :
    ¬ marker ≤ reported - error - ageLoss := by omega

theorem detection_for_all_bounded_errors (current sampled reported error ageLoss marker : Int)
    (rateLower : current - ageLoss ≤ sampled)
    (readLower : sampled - error ≤ reported)
    (detected : marker + 2*error + 2*ageLoss ≤ current) :
    marker ≤ reported - error - ageLoss := by omega

theorem cutoff_beyond_response (detected cutoff position travel : Int)
    (geometry : detected + travel < cutoff)
    (rateBound : position ≤ detected + travel) : position < cutoff := by omega

/-- A response may take J to latch; a later repeated command is needed after
all older zero commands arrive when delivery order is unconstrained. -/
theorem persistent_command_by (detected response delay latched lastZeroArrived
    freshIssued freshArrived : Int)
    (latch : latched ≤ detected + response)
    (zeros : lastZeroArrived ≤ latched + delay)
    (afterZeros : lastZeroArrived < freshIssued)
    (reissue : freshIssued ≤ lastZeroArrived + response)
    (causal : freshIssued ≤ freshArrived)
    (deliver : freshArrived ≤ freshIssued + delay) :
    lastZeroArrived < freshArrived ∧
      freshArrived ≤ detected + 2*response + 2*delay := by omega

theorem entry_command_drain (entry response delay oldArrived clearIssued clearArrived
    unlock : Int)
    (old : oldArrived ≤ entry + delay)
    (afterOld : oldArrived < clearIssued)
    (clear : clearIssued ≤ oldArrived + response)
    (causal : clearIssued ≤ clearArrived)
    (delivery : clearArrived ≤ clearIssued + delay)
    (travel : entry + response + 2*delay < unlock) :
    oldArrived < clearArrived ∧ clearArrived < unlock := by omega

theorem closure_after_settlement (position : Nat → Nat) (settled limit : Nat)
    (steps : ∀ n, min limit (position (settled+n)+1) ≤ position (settled+(n+1))) :
    limit ≤ position (settled+limit) := by
  have lower : ∀ n, min limit n ≤ position (settled+n) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hn := steps n
      omega
  have h := lower limit
  omega

def writeAt {Cell : Type} (image : Nat → Cell) (address : Nat) (value : Cell) : Nat → Cell :=
  fun j => if j = address then value else image j

theorem expected_write_preserves_complete_image {Cell : Type}
    (image reference : Nat → Cell) (address : Nat) (value : Cell)
    (complete : image = reference) (expected : value = reference address) :
    writeAt image address value = reference := by
  subst image
  subst value
  funext j
  unfold writeAt
  split
  · rename_i same
    subst j
    rfl
  · rfl

theorem scale_ten_small_motion_obstruction :
    (20+11-30 : Int) = 1 ∧ (20-20 : Int) ≤ 30 ∧
    (-30 : Int) ≤ 20-20 ∧ (0-2-20 : Int) < 5 := by decide

theorem positive_noise_is_not_positive_position :
    (0 : Int) < 2 ∧ ¬ (1 : Int) ≤ 2-2 := by decide

#print axioms robust_join_sound
#print axioms reset_zero_cannot_join
#print axioms detection_for_all_bounded_errors
#print axioms cutoff_beyond_response
#print axioms persistent_command_by
#print axioms entry_command_drain
#print axioms closure_after_settlement
#print axioms expected_write_preserves_complete_image
#print axioms scale_ten_small_motion_obstruction
#print axioms positive_noise_is_not_positive_position
end ByzantineNoisyClamp
