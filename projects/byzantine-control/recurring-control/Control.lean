import Std

/-! Selected integer policy, timing, access and arithmetic certificates.
The real-valued source/control and resource proofs are in CONTROL.md.
This file does not claim a mechanization of the complete physical source. -/
namespace ByzantineRecurringControl

def correction (m : Int) : Int :=
  if m > 53 then min 1500 ((8 * (m - 53)) / 5)
  else if m < -53 then -min 1500 ((8 * (-m - 53)) / 5)
  else 0

theorem correction_bounds (m : Int) :
    -1500 ≤ correction m ∧ correction m ≤ 1500 := by
  unfold correction
  split
  · omega
  · split <;> omega

theorem positive_requires_guard (m : Int) (h : 0 < correction m) : 53 < m := by
  unfold correction at h
  split at h
  · omega
  · split at h <;> omega

theorem negative_requires_guard (m : Int) (h : correction m < 0) : m < -53 := by
  unfold correction at h
  split at h
  · omega
  · split at h <;> omega

/-- Truth is represented here in millionths; the analytic real-valued
version follows the same order argument without a grid restriction. -/
theorem positive_factive_duty (m x : Int)
    (herr : m*1000-3000 ≤ x) (h : 0 < correction m) : 50000 ≤ x := by
  have := positive_requires_guard m h
  omega

theorem negative_factive_duty (m x : Int)
    (herr : x ≤ m*1000+3000) (h : correction m < 0) : x ≤ -50000 := by
  have := negative_requires_guard m h
  omega

theorem good_radius_command_bound (m : Int) (hl : -803 ≤ m) (hu : m ≤ 803) :
    -1200 ≤ correction m ∧ correction m ≤ 1200 := by
  unfold correction
  split
  · omega
  · split <;> omega

/-- Clearing denominator5 certifies the deadband plus rounding error;
the constant429 is conservative (the exact integer bound is428). -/
theorem soft_bias_scaled (m : Int) (hl : -803 ≤ m) (hu : m ≤ 803) :
    -429 ≤ 5*correction m-8*m ∧ 5*correction m-8*m ≤ 429 := by
  unfold correction
  split
  · omega
  · split <;> omega

theorem word_product_bound (m : Int) (hl : -4000 ≤ m) (hu : m ≤ 4000) :
    -32000 ≤ 8*m ∧ 8*m ≤ 32000 := by omega

/-- A causal last-arrival relation gives2L held age even with reordering. -/
theorem held_age_from_latest_arrival (t lag issued anchor arrival : Int)
    (href : t-lag ≤ anchor) (hlatest : anchor ≤ arrival)
    (hdelay : arrival ≤ issued+lag) (hcausal : issued ≤ arrival)
    (hdelivered : arrival ≤ t) : t-2*lag ≤ issued ∧ issued ≤ t := by omega

theorem generic_feedback_flush (t lag first issued : Int)
    (hage : t-2*lag ≤ issued) (htime : first+2*lag ≤ t) : first ≤ issued := by omega

/-- If all baseline arrivals precede first feedback issuance, a later last
arrival cannot be baseline. This is the actual quiet-drain obligation. -/
theorem quiet_drain_excludes_baseline (oldLast first freshArrival heldArrival : Int)
    (hgap : oldLast < first) (hcausal : first ≤ freshArrival)
    (hlatest : freshArrival ≤ heldArrival) : oldLast < heldArrival := by omega

/-- Quarter-unit lower-envelope propagation after four actual deployment steps. -/
theorem four_access_steps (a0 a1 a2 a3 a4 : Int) (h0 : 0 ≤ a0)
    (h1 : min 4 (a0+1) ≤ a1) (h2 : min 4 (a1+1) ≤ a2)
    (h3 : min 4 (a2+1) ≤ a3) (h4 : min 4 (a3+1) ≤ a4) : 4 ≤ a4 := by omega

theorem startup_service_equal : (3*17 : Int) < 7*10 := by decide

theorem startup_service_weighted : (3*170 : Int) < 67*10 := by decide

theorem equal_invariance_margin : (0 : Int) < 40909 := by decide

theorem weighted_invariance_margin : (0 : Int) < 1803 := by decide

theorem recurrent_service_equal : (3*85 : Int) < 58*10 := by decide

theorem recurrent_service_weighted : (3*85 : Int) < 56*10 := by decide

theorem coefficient_nonnegative : (0 : Int) < 19999999689 := by decide

theorem current_and_effect_error_fit :
    (2000576851*1000 : Int) < 3*1000000000000 := by decide

theorem source_operation_cap : (2*34+2*34+34+34+1 : Int) = 205 := by decide

theorem pointwise_resource_cap :
    (456000000+28000000+6800000+139264+68000000+34000000+34000000+272000000+2000000 : Int) = 900939264 := by decide

theorem source_supply_fits : (900939264 : Int) ≤ 901000000 ∧ (901000000 : Int) ≤ 1000000000 := by decide

theorem initial_sample_reserve : (1000-2*2*34 : Int) = 864 ∧ (0 : Int) < 864 := by decide

theorem stock_after_extra (stock lower supply ordinary extra capacity : Int)
    (hstock : lower ≤ stock) (hcost : ordinary ≤ supply)
    (hcap : lower ≤ capacity) (hextra : 0 ≤ extra) :
    lower-extra ≤ min capacity (stock+supply-ordinary-extra) := by omega

theorem startup_radius_fits : (125000157323*5 : Int) < 4*250000000000 := by decide

theorem source_resource_exhaustion : (1500 : Int) < 89*17 := by decide

theorem paid_stock_nonnegative (stock supply cost capacity : Int)
    (hcap : 0 ≤ capacity) (hpay : cost ≤ stock+supply) :
    0 ≤ min capacity (stock+supply-cost) := by omega

theorem stock_nondecreasing (stock supply cost capacity : Int)
    (hcap : stock ≤ capacity) (hcost : cost ≤ supply) :
    stock ≤ min capacity (stock+supply-cost) := by omega

theorem envelope_step (next linear disturbance bound reserve : Int)
    (hnext : next ≤ linear+disturbance) (hlinear : linear ≤ bound-reserve)
    (hdisturbance : disturbance ≤ reserve) : next ≤ bound := by omega

#print axioms correction_bounds
#print axioms positive_requires_guard
#print axioms negative_requires_guard
#print axioms positive_factive_duty
#print axioms negative_factive_duty
#print axioms good_radius_command_bound
#print axioms soft_bias_scaled
#print axioms word_product_bound
#print axioms held_age_from_latest_arrival
#print axioms generic_feedback_flush
#print axioms quiet_drain_excludes_baseline
#print axioms four_access_steps
#print axioms startup_service_equal
#print axioms startup_service_weighted
#print axioms equal_invariance_margin
#print axioms weighted_invariance_margin
#print axioms recurrent_service_equal
#print axioms recurrent_service_weighted
#print axioms coefficient_nonnegative
#print axioms current_and_effect_error_fit
#print axioms source_operation_cap
#print axioms pointwise_resource_cap
#print axioms source_supply_fits
#print axioms initial_sample_reserve
#print axioms stock_after_extra
#print axioms startup_radius_fits
#print axioms source_resource_exhaustion
#print axioms paid_stock_nonnegative
#print axioms stock_nondecreasing
#print axioms envelope_step
end ByzantineRecurringControl
