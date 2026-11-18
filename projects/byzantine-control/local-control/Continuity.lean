import Std

namespace ByzantineLocalContinuity

-- Integer/rationally scaled elapsed times are analytical coordinates only.
theorem geometry_ready_overlap
    (power ready oldOff transit startup work : Int)
    (geometry : transit ≤ oldOff-power)
    (startupPrefix : ready-power ≤ startup)
    (margin : startup+work ≤ transit) : ready+work ≤ oldOff := by omega

theorem ready_before_old_disconnect
    (ready response applied oldOff : Int)
    (bounded : applied ≤ ready+response)
    (overlap : ready+response ≤ oldOff) : applied ≤ oldOff := by omega

theorem applied_response_before_retirement
    (ready emitted applied retire localWork delivery : Int)
    (emission : emitted ≤ ready+localWork)
    (transport : applied ≤ emitted+delivery)
    (overlap : ready+localWork+delivery ≤ retire) : applied ≤ retire := by omega

theorem interval_cover_through
    (begins ends : Nat → Nat) (work t k : Nat)
    (initial : begins 0 = 0)
    (overlap : ∀ j, begins (j+1)+work ≤ ends j)
    (endpoint : t+work ≤ ends k) :
    ∃ j, j ≤ k ∧ begins j ≤ t ∧ t+work ≤ ends j := by
  induction k with
  | zero => exact ⟨0, by omega, by omega, endpoint⟩
  | succ k ih =>
    by_cases earlier : t+work ≤ ends k
    · obtain ⟨j,hj,hbegin,hend⟩ := ih earlier
      exact ⟨j, by omega, hbegin, hend⟩
    · exact ⟨k+1, by omega, by have h := overlap k; omega, endpoint⟩

theorem ready_interval_cover
    (begins ends : Nat → Nat) (work : Nat)
    (initial : begins 0 = 0)
    (overlap : ∀ j, begins (j+1)+work ≤ ends j)
    (unbounded : ∀ q, ∃ k, q ≤ ends k) (t : Nat) :
    ∃ j, begins j ≤ t ∧ t+work ≤ ends j := by
  obtain ⟨k,hk⟩ := unbounded (t+work)
  obtain ⟨j,_,hbegin,hend⟩ := interval_cover_through begins ends work t k initial overlap hk
  exact ⟨j,hbegin,hend⟩

-- The elapsed bound includes a possible partly completed visit at eligibility.
theorem round_robin_response_bound (degree before visit elapsed : Nat)
    (distance : before < degree)
    (steps : elapsed ≤ (before+2)*visit) :
    elapsed ≤ (degree+1)*visit := by
  have h : before+2 ≤ degree+1 := by omega
  exact Nat.le_trans steps (Nat.mul_le_mul_right visit h)

theorem window_contains_response
    (t work begin finish completion : Int)
    (cover : begin ≤ t ∧ t+work ≤ finish)
    (response : t ≤ completion ∧ completion ≤ t+work) :
    begin ≤ completion ∧ completion ≤ finish := by omega

theorem insufficient_single_interval (a b t work : Int)
    (short : b-a < work) : ¬ (a ≤ t ∧ t+work ≤ b) := by omega

def drySpeed (force threshold : Int) : Int :=
  if threshold < force then force-threshold
  else if force < -threshold then force+threshold else 0

theorem stiction_prevents_reverse (force threshold : Int)
    (low : -threshold ≤ force) : 0 ≤ drySpeed force threshold := by
  unfold drySpeed
  split
  · omega
  · split <;> omega

theorem positive_force_progress (force threshold margin : Int)
    (positive : 0 < margin) (support : threshold+margin ≤ force) :
    margin ≤ drySpeed force threshold := by
  have h : threshold < force := by omega
  simp [drySpeed,h]
  omega

theorem persistent_increment (x : Nat → Nat) (gain : Nat)
    (step : ∀ k, x k+gain ≤ x (k+1)) :
    ∀ k, x 0+k*gain ≤ x k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have next := step k
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem reached_by_accumulated_progress (initial gain steps target current : Nat)
    (progress : initial+steps*gain ≤ current)
    (enough : target ≤ initial+steps*gain) : target ≤ current := by omega

theorem guard_distance_absorbs_age
    (trigger observedAt actualLater error travel guard : Int)
    (observation : observedAt ≤ trigger+2*error)
    (motion : actualLater ≤ observedAt+travel)
    (margin : 2*error+travel < guard) : actualLater < trigger+guard := by omega

theorem two_bank_force_bound (a b perBank : Int)
    (ha : -perBank ≤ a ∧ a ≤ perBank)
    (hb : -perBank ≤ b ∧ b ≤ perBank) :
    -(2*perBank) ≤ a+b ∧ a+b ≤ 2*perBank := by omega

theorem doubled_force_can_cross_limit : (2 : Int) ≤ 3 ∧ 2+2 > 3 := by decide

theorem reverse_force_counterexample : drySpeed (-3) 2 = -1 := by decide

theorem uninitialized_bank_force_counterexample :
    drySpeed (34*(20-22)-6*44-10) 280 = -62 := by decide

-- A delayed physical effect can occur strictly after removing sender power.
theorem old_command_after_power_off : (0 : Nat) < 1 ∧ 1 < 2 := by decide

#print axioms geometry_ready_overlap
#print axioms ready_before_old_disconnect
#print axioms applied_response_before_retirement
#print axioms interval_cover_through
#print axioms ready_interval_cover
#print axioms round_robin_response_bound
#print axioms window_contains_response
#print axioms insufficient_single_interval
#print axioms stiction_prevents_reverse
#print axioms positive_force_progress
#print axioms persistent_increment
#print axioms reached_by_accumulated_progress
#print axioms guard_distance_absorbs_age
#print axioms two_bank_force_bound
#print axioms doubled_force_can_cross_limit
#print axioms reverse_force_counterexample
#print axioms uninitialized_bank_force_counterexample
#print axioms old_command_after_power_off

end ByzantineLocalContinuity
