import Std

/-! Kernel-checked integer certificates obtained by clearing the positive
rational denominators stated in CONTROL.md. The real-valued norm/source
arguments remain mathematical proofs there. No floating-point or native-decide
axiom is used, and these checks do not claim full source mechanization. -/
namespace ByzantineJointControl

/-- B=2377/3250 < lambda*R=2594/3250. -/
theorem strict_invariance_margin : (2377 : Int) < 2594 := by decide

/-- 1-delta*(k-a_min)=199689/200000 is positive. -/
theorem coefficient_nonnegative : (0 : Int) < 199689 := by decide

/-- Actual per-coordinate service floor54/125 exceeds3/10. -/
theorem strict_actual_service : (3*125 : Int) < 54*10 := by decide

/-- Prescribed actual good-path command magnitude172/125 is below2. -/
theorem command_within_physical_limit : (172 : Int) < 2*125 := by decide

/-- Effect error10749/200000 includes20tick information age,4tick
actuation age, and1/1000 command rounding divided by gain8/5. -/
theorem actual_delay_and_quantization_fit : (10749*50 : Int) ≤ 3*200000 := by decide

/-- Full source start radius1/2 grows to at most6889/12500 in24ticks. -/
theorem full_initial_query_fits_startup : (6889*5 : Int) < 4*12500 := by decide

/-- One pool pays all inference, ordinary actuation, rogue inquiry and repair. -/
theorem resource_rate : (104+1300+4+13*25 : Int) < 1734 := by decide

theorem query_burst : (13*500 : Int) = 6500 := by decide

theorem operation_side_effect : (810*100 : Int) < 100000 := by decide

/-- Once8/13 channels retain poisoned output-2, even maximal honest
response leaves positive mean drift47/130000 throughout the safe box. -/
theorem no_repair_drift : (0 : Int) < 47 := by decide

theorem no_repair_escape_bound : (2*130000 : Int) < 5532*47 := by decide

/-- Unequal influence weights retain a strict radius margin921/16250. -/
theorem heterogeneous_margin : (0 : Int) < 921 := by decide

theorem heterogeneous_service : (3*3125 : Int) < 1344*10 := by decide

theorem initial_contamination_phase_safe :
    (12159729223*5 : Int) < 4*16250000000 := by decide

/-- Insufficient stock is not hidden by deleting a transition. The interval
argument establishes hpay for every actual demanded operation. -/
theorem paid_stock_nonnegative (stock supply cost capacity : Int)
    (hcapacity : 0 ≤ capacity) (hpay : cost ≤ stock+supply) :
    0 ≤ min capacity (stock+supply-cost) := by omega

/-- Elementary one-step envelope rule after deriving actual norm terms. -/
theorem envelope_step (next linear disturbance bound reserve : Int)
    (hnext : next ≤ linear+disturbance)
    (hlinear : linear ≤ bound-reserve)
    (hdisturbance : disturbance ≤ reserve) : next ≤ bound := by omega

#print axioms strict_invariance_margin
#print axioms coefficient_nonnegative
#print axioms strict_actual_service
#print axioms command_within_physical_limit
#print axioms actual_delay_and_quantization_fit
#print axioms full_initial_query_fits_startup
#print axioms resource_rate
#print axioms query_burst
#print axioms operation_side_effect
#print axioms no_repair_drift
#print axioms no_repair_escape_bound
#print axioms heterogeneous_margin
#print axioms heterogeneous_service
#print axioms initial_contamination_phase_safe
#print axioms paid_stock_nonnegative
#print axioms envelope_step
end ByzantineJointControl
