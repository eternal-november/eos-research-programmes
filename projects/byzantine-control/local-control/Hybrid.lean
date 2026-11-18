import Std

/-! Selected order obligations for HYBRID.md; not a mechanization of continuous existence. -/
namespace ByzantineHybrid

theorem persistent_permission (b0 z0 b z load : Int)
    (bEntry : 600 ≤ b0) (zEntry : 800 ≤ z0)
    (bRetained : b0 ≤ b) (zRetained : z0 ≤ z)
    (actualLoad : load ≤ 2 * (1000-b) + 200) :
    load ≤ 1000 ∧ 800 ≤ z := by omega

theorem current_lower_bound (actual sample report error ageLoss : Int)
    (reported : report ≤ sample + error) (variation : sample ≤ actual + ageLoss) :
    report-error-ageLoss ≤ actual := by omega

theorem post_tail_sample (cut tail age reply sample : Int)
    (fresh : reply-age ≤ sample) (wait : cut+tail+age < reply) :
    cut+tail < sample := by omega

theorem bounded_clock_wait (elapsed localWait tail age : Int)
    (fastClock : 100*localWait ≤ 101*elapsed)
    (wait : 101*(tail+age) < 100*localWait) : tail+age < elapsed := by omega

theorem selected_wait_boundaries :
    (101*823 : Int) < 83300 ∧ (83300 : Int) < 101*(823+6) ∧
    (101*(823+6) : Int) < 83900 := by decide

theorem sampled_stop_remains_stop (sample current stop : Int)
    (contact : sample = stop) (retained : sample ≤ current)
    (physicalStop : current ≤ stop) : current = stop := by omega

theorem post_stage_contact_sample (entry age sample reply : Int)
    (boundedAge : reply-age ≤ sample) (wait : entry+age < reply) : entry < sample := by omega

theorem separated_old_force_tail (opened tail lastOld newGate : Int)
    (lastEffect : lastOld ≤ opened+tail) (deadTravel : opened+tail < newGate) :
    lastOld < newGate := by omega

theorem funded_completion_tail (reserved spent remaining : Int)
    (funded : spent ≤ reserved) (ledger : remaining = reserved-spent) :
    0 ≤ remaining := by omega

abbrev Image (n : Nat) (Cell : Type) := Fin n → Cell

def writeAt {n : Nat} {Cell : Type} (image : Image n Cell)
    (address : Fin n) (value : Cell) : Image n Cell :=
  fun a => if a = address then value else image a

theorem expected_commit_preserves_image {n : Nat} {Cell : Type}
    (reference : Image n Cell) (address : Fin n) :
    writeAt reference address (reference address) = reference := by
  funext a
  unfold writeAt
  split
  · rename_i h
    subst a
    rfl
  · rfl

def expectedCommits {n : Nat} {Cell : Type} (reference : Image n Cell) :
    List (Fin n) → Image n Cell → Image n Cell
  | [], image => image
  | a::rest, image => expectedCommits reference rest (writeAt image a (reference a))

theorem arbitrary_expected_commit_order {n : Nat} {Cell : Type}
    (reference : Image n Cell) (addresses : List (Fin n)) :
    expectedCommits reference addresses reference = reference := by
  induction addresses with
  | nil => rfl
  | cons a rest ih =>
    simp only [expectedCommits, expected_commit_preserves_image]
    exact ih

theorem zero_is_not_conjunction_identity :
    (false && true) = false ∧ (true && true) = true := by decide


theorem direct_functional_permission
    (load reportLoad errorLoad variationLoad isolation reportIsolation errorIsolation variationIsolation : Int)
    (actualLoad : load ≤ reportLoad+errorLoad+variationLoad)
    (actualIsolation : reportIsolation-errorIsolation-variationIsolation ≤ isolation)
    (loadGuard : reportLoad+errorLoad+variationLoad ≤ 1000)
    (isolationGuard : 800 ≤ reportIsolation-errorIsolation-variationIsolation) :
    load ≤ 1000 ∧ 800 ≤ isolation := by omega

theorem nominal_withdrawal_bound
    (lastPositive delay response forceTail retireTail lastOld clearIssued clearApplied fieldOff : Int)
    (oldBound : lastOld ≤ lastPositive+delay)
    (freshZero : clearIssued ≤ lastOld+response)
    (application : clearApplied ≤ clearIssued+delay)
    (withdrawal : fieldOff ≤ clearApplied+forceTail+retireTail) :
    fieldOff ≤ lastPositive+response+2*delay+forceTail+retireTail := by omega


theorem same_word_range_has_circular_lift
    (candidate sample liftedCurrent radius beta : Int)
    (rangeLower : candidate-radius ≤ sample) (rangeUpper : sample ≤ candidate+radius)
    (sampleLower : sample-beta ≤ liftedCurrent) (sampleUpper : liftedCurrent ≤ sample+beta) :
    candidate-(radius+beta) ≤ liftedCurrent ∧ liftedCurrent ≤ candidate+(radius+beta) := by omega

theorem old_entering_cannot_survive_return
    (lastEntering full normal sample age : Int)
    (ended : lastEntering < full) (travel : full+age < normal)
    (fresh : normal-age ≤ sample) (wasEntering : sample ≤ lastEntering) : False := by omega

theorem return_contact_words_exclude_entering (word : Nat)
    (returnWord : word = 3 ∨ word = 1 ∨ word = 0) : word ≠ 2 := by omega

theorem certified_refresh_implies_actual_gain
    (oldActual newActual oldUpper newLower quantum : Int)
    (upper : oldActual ≤ oldUpper) (lower : newLower ≤ newActual)
    (refresh : oldUpper+quantum < newLower) : oldActual+quantum < newActual := by omega

theorem gain_beyond_four_errors_forces_refresh
    (oldActual newActual oldEstimate newEstimate error quantum : Int)
    (oldBound : oldEstimate ≤ oldActual+error)
    (newBound : newActual-error ≤ newEstimate)
    (gain : oldActual+quantum+4*error < newActual) :
    oldEstimate+error+quantum < newEstimate-error := by omega

theorem small_rank_bin_prevents_second_refresh
    (atFirst atSecond firstUpper secondLower quantum : Int)
    (smallBin : atSecond ≤ atFirst+quantum)
    (upper : atFirst ≤ firstUpper) (lower : secondLower ≤ atSecond) :
    ¬ firstUpper+quantum < secondLower := by omega

theorem escrow_refund_preserves_total
    (beforeFree beforeReserved afterFree afterReserved refund : Int)
    (freeUpdate : afterFree = beforeFree+refund)
    (reservedUpdate : afterReserved = beforeReserved-refund) :
    afterFree+afterReserved = beforeFree+beforeReserved := by omega


theorem seven_distinct_producers_not_all_in_six
    (covered producers : Int) (coverBound : covered ≤ 6)
    (producerCount : producers = 7) (allCovered : producers ≤ covered) : False := by omega

theorem donor_finishes_before_derived_deadline
    (cue elapsed localWait copyBound completed firstClose : Int)
    (fastClock : 100*localWait ≤ 101*elapsed)
    (deadline : 101*copyBound < 100*localWait)
    (rawCopy : completed ≤ cue+copyBound)
    (closeTime : cue+elapsed ≤ firstClose) : completed < firstClose := by omega

#print axioms persistent_permission
#print axioms current_lower_bound
#print axioms post_tail_sample
#print axioms bounded_clock_wait
#print axioms selected_wait_boundaries
#print axioms sampled_stop_remains_stop
#print axioms post_stage_contact_sample
#print axioms separated_old_force_tail
#print axioms funded_completion_tail
#print axioms expected_commit_preserves_image
#print axioms arbitrary_expected_commit_order
#print axioms zero_is_not_conjunction_identity
#print axioms direct_functional_permission
#print axioms nominal_withdrawal_bound
#print axioms same_word_range_has_circular_lift
#print axioms old_entering_cannot_survive_return
#print axioms return_contact_words_exclude_entering
#print axioms certified_refresh_implies_actual_gain
#print axioms gain_beyond_four_errors_forces_refresh
#print axioms small_rank_bin_prevents_second_refresh
#print axioms escrow_refund_preserves_total
#print axioms seven_distinct_producers_not_all_in_six
#print axioms donor_finishes_before_derived_deadline
end ByzantineHybrid
