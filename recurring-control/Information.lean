import Std

/-! Discrete information/recency core for INFORMATION.md.
The actual bytecode and physical-source refinements have written arguments and
executable checks; this module does not claim their complete mechanization. -/
namespace RecurringInformation

theorem count_mono_on {α : Type} (p q : α → Bool) (xs : List α)
    (imp : ∀ x ∈ xs, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have tail : ∀ x ∈ xs, p x = true → q x = true :=
      fun x hx hp => imp x (by simp [hx]) hp
    have htail := ih tail
    have head := imp a (by simp)
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem count_all {α : Type} (p : α → Bool) (xs : List α)
    (all : ∀ x ∈ xs, p x = true) : xs.countP p = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := all a (by simp)
    have ht : ∀ x ∈ xs, p x = true := fun x hx => all x (by simp [hx])
    simp [ha, ih ht]

abbrev Row := Int × Bool
def faulty (r : Row) : Bool := !r.2
def below (lo : Int) (r : Row) : Bool := decide (r.1 < lo)
def above (hi : Int) (r : Row) : Bool := decide (hi < r.1)

theorem below_bounded_by_faults (rows : List Row) (lo : Int)
    (sound : ∀ r ∈ rows, r.2 = true → lo ≤ r.1) :
    rows.countP (below lo) ≤ rows.countP faulty := by
  apply count_mono_on
  intro r hr hb
  have hlt : r.1 < lo := by simpa [below] using hb
  cases hgood : r.2 with
  | false => simp [faulty, hgood]
  | true =>
    have hge := sound r hr hgood
    omega

theorem above_bounded_by_faults (rows : List Row) (hi : Int)
    (sound : ∀ r ∈ rows, r.2 = true → r.1 ≤ hi) :
    rows.countP (above hi) ≤ rows.countP faulty := by
  apply count_mono_on
  intro r hr hb
  have hlt : hi < r.1 := by simpa [above] using hb
  cases hgood : r.2 with
  | false => simp [faulty, hgood]
  | true =>
    have hle := sound r hr hgood
    omega

theorem median_from_counts (before after : List Row) (middle : Row)
    (lo hi : Int) (q : Nat)
    (hlen : before.length = q) (hlen' : after.length = q)
    (left_order : ∀ r ∈ before, r.1 ≤ middle.1)
    (right_order : ∀ r ∈ after, middle.1 ≤ r.1)
    (lower_count : (before ++ middle :: after).countP (below lo) ≤ q)
    (upper_count : (before ++ middle :: after).countP (above hi) ≤ q) :
    lo ≤ middle.1 ∧ middle.1 ≤ hi := by
  constructor
  · by_cases h : lo ≤ middle.1
    · exact h
    have hm : middle.1 < lo := by omega
    exfalso
    have hb : before.countP (below lo) = q := by
      rw [count_all, hlen]
      intro r hr
      have hp := left_order r hr
      simp [below]
      omega
    have hmid : below lo middle = true := by simp [below, hm]
    simp [List.countP_append, hmid, hb] at lower_count <;> omega
  · by_cases h : middle.1 ≤ hi
    · exact h
    have hm : hi < middle.1 := by omega
    exfalso
    have ha : after.countP (above hi) = q := by
      rw [count_all, hlen']
      intro r hr
      have hp := right_order r hr
      simp [above]
      omega
    have hmid : above hi middle = true := by simp [above, hm]
    simp [List.countP_append, hmid, ha] at upper_count <;> omega

theorem robust_rank_median (before after : List Row) (middle : Row)
    (lo hi : Int) (q : Nat)
    (hlen : before.length = q) (hlen' : after.length = q)
    (left_order : ∀ r ∈ before, r.1 ≤ middle.1)
    (right_order : ∀ r ∈ after, middle.1 ≤ r.1)
    (budget : (before ++ middle :: after).countP faulty ≤ q)
    (sound : ∀ r ∈ before ++ middle :: after,
      r.2 = true → lo ≤ r.1 ∧ r.1 ≤ hi) :
    lo ≤ middle.1 ∧ middle.1 ≤ hi := by
  apply median_from_counts before after middle lo hi q hlen hlen' left_order right_order
  · exact Nat.le_trans (below_bounded_by_faults _ lo
      (fun r hr hg => (sound r hr hg).1)) budget
  · exact Nat.le_trans (above_bounded_by_faults _ hi
      (fun r hr hg => (sound r hr hg).2)) budget

theorem fault_budget_under_permutation (a b : List Row) (h : a.Perm b) (q : Nat)
    (hb : b.countP faulty ≤ q) : a.countP faulty ≤ q := by
  rw [h.countP_eq faulty]
  exact hb

theorem source_group_has_margin : (5 : Nat) ≤ 8 ∧ 17 = 2*8+1 := by decide

theorem sample_age_bound (sample emitted now period latency : Nat)
    (emit_delay : emitted ≤ sample+1)
    (recent : now < emitted+period+latency+1) :
    now-sample ≤ period+latency+1 := by omega

theorem held_effect_age (issued arrived now delay : Nat)
    (recent_arrival : now ≤ arrived+delay)
    (arrival_bound : arrived ≤ issued+delay) :
    now-issued ≤ 2*delay := by omega

theorem quiet_baseline_expires_before_feedback (boot fallback fresh : Nat)
    (old : fallback ≤ boot+4) (new : boot+16 ≤ fresh) :
    fallback < fresh := by omega

theorem combined_information_effect_age : (13 : Nat)+2*4 = 21 := by decide

/-- .002 + 21 * 10^-8 * 2.62205 < .003 after positive-denominator clearing. -/
theorem source_error_margin : (20005506305 : Int) < 30000000000 := by decide

theorem positive_milliunit_trigger (measured : Int) (h : 53 < measured) :
    50 ≤ measured-3 := by omega

theorem negative_milliunit_trigger (measured : Int) (h : measured < -53) :
    measured+3 ≤ -50 := by omega

theorem future_phase_numerator (base k m : Nat) :
    base+4+k+m+1-k = base+m+5 := by omega

#print axioms count_mono_on
#print axioms count_all
#print axioms below_bounded_by_faults
#print axioms above_bounded_by_faults
#print axioms median_from_counts
#print axioms robust_rank_median
#print axioms fault_budget_under_permutation
#print axioms source_group_has_margin
#print axioms sample_age_bound
#print axioms held_effect_age
#print axioms quiet_baseline_expires_before_feedback
#print axioms combined_information_effect_age
#print axioms source_error_margin
#print axioms positive_milliunit_trigger
#print axioms negative_milliunit_trigger
#print axioms future_phase_numerator
end RecurringInformation

