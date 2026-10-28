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
end ByzantineHybrid
