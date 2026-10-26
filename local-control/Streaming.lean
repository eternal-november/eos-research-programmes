import Std

/-! Count/search implications for STREAMING.md. The actual I/C/W capability
map, machine realization and physical observation envelope are separate. -/
namespace LocalStreaming

abbrev Row := Nat × Bool
def bad (r : Row) : Bool := !r.2
def below (p : Nat) (r : Row) : Bool := decide (r.1 ≤ p)
def above (p : Nat) (r : Row) : Bool := decide (p ≤ r.1)

theorem count_mono {α : Type} (f g : α → Bool) (xs : List α)
    (imp : ∀ x ∈ xs, f x = true → g x = true) :
    xs.countP f ≤ xs.countP g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := imp x (by simp)
    have tail : ∀ y ∈ xs, f y = true → g y = true :=
      fun y hy hf => imp y (by simp [hy]) hf
    have ht := ih tail
    cases hf : f x <;> cases hg : g x <;> simp_all <;> omega

theorem count_partition (rows : List Row) :
    rows.countP (fun r => r.2) + rows.countP bad = rows.length := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    cases h : r.2 <;> simp_all [bad] <;> omega

theorem good_majority (rows : List Row) (q : Nat)
    (length : rows.length = 2*q+1) (budget : rows.countP bad ≤ q) :
    q < rows.countP (fun r => r.2) := by
  have h := count_partition rows
  omega

theorem passing_threshold_above_lower (rows : List Row) (q lower pivot : Nat)
    (budget : rows.countP bad ≤ q)
    (sound : ∀ r ∈ rows, r.2 = true → lower ≤ r.1)
    (pass : q < rows.countP (below pivot)) : lower ≤ pivot := by
  by_cases h : lower ≤ pivot
  · exact h
  · have limited : rows.countP (below pivot) ≤ rows.countP bad := by
      apply count_mono
      intro r hr hp
      have hvalue : r.1 ≤ pivot := by simpa [below] using hp
      cases hg : r.2 with
      | false => simp [bad, hg]
      | true =>
        have hs := sound r hr hg
        omega
    omega

theorem failing_threshold_below_upper (rows : List Row) (q upper pivot : Nat)
    (majority : q < rows.countP (fun r => r.2))
    (sound : ∀ r ∈ rows, r.2 = true → r.1 ≤ upper)
    (fail : rows.countP (below pivot) ≤ q) : pivot < upper := by
  by_cases h : pivot < upper
  · exact h
  · have dominated : rows.countP (fun r => r.2) ≤ rows.countP (below pivot) := by
      apply count_mono
      intro r hr hg
      have hs := sound r hr hg
      simp [below]
      omega
    omega

theorem passing_high_threshold_below_upper (rows : List Row) (q upper pivot : Nat)
    (budget : rows.countP bad ≤ q)
    (sound : ∀ r ∈ rows, r.2 = true → r.1 ≤ upper)
    (pass : q < rows.countP (above pivot)) : pivot ≤ upper := by
  by_cases h : pivot ≤ upper
  · exact h
  · have limited : rows.countP (above pivot) ≤ rows.countP bad := by
      apply count_mono
      intro r hr hp
      have hvalue : pivot ≤ r.1 := by simpa [above] using hp
      cases hg : r.2 with
      | false => simp [bad, hg]
      | true =>
        have hs := sound r hr hg
        omega
    omega

theorem midpoint_inside (lo hi : Nat) (strict : lo < hi) :
    lo ≤ (lo+hi)/2 ∧ (lo+hi)/2 < hi := by omega

theorem width_after_pass (lo hi : Nat) (ordered : lo ≤ hi) :
    (lo+hi)/2-lo ≤ (hi-lo)/2 := by omega

theorem width_after_fail (lo hi : Nat) (strict : lo < hi) :
    hi-((lo+hi)/2+1) ≤ (hi-lo)/2 := by omega

theorem pass_preserves_envelope (lo hi lower upper pivot : Nat)
    (invariant : lower ≤ hi ∧ lo ≤ upper)
    (witness : lower ≤ pivot) : lower ≤ pivot ∧ lo ≤ upper :=
  ⟨witness, invariant.2⟩

theorem fail_preserves_envelope (lo hi lower upper pivot : Nat)
    (invariant : lower ≤ hi ∧ lo ≤ upper)
    (witness : pivot < upper) : lower ≤ hi ∧ pivot+1 ≤ upper := by omega

theorem terminal_envelope (lo hi lower upper : Nat)
    (invariant : lower ≤ hi ∧ lo ≤ upper) (done : lo = hi) :
    lower ≤ lo ∧ lo ≤ upper := by omega

theorem finite_width_decreases (width next : Nat)
    (positive : 0 < width) (half : next ≤ width/2) : next < width := by omega

theorem permission_from_actual_sample (actual sample threshold error drift limit : Int)
    (observed : sample ≤ threshold)
    (cover : actual ≤ sample+error+drift)
    (guard : threshold+error+drift ≤ limit) : actual ≤ limit := by omega

theorem isolation_from_actual_sample (actual sample threshold error drift minimum : Int)
    (observed : threshold ≤ sample)
    (cover : sample-error-drift ≤ actual)
    (guard : minimum ≤ threshold-error-drift) : minimum ≤ actual := by omega

theorem complementary_numerator_error (es ed bs bd : Int)
    (hs : -bs ≤ es ∧ es ≤ bs) (hd : -bd ≤ ed ∧ ed ≤ bd) :
    -(bs+bd) ≤ es+ed ∧ es+ed ≤ bs+bd ∧
    -(bs+bd) ≤ es-ed ∧ es-ed ≤ bs+bd := by omega

theorem read_work_bound (reads slots passes passBound : Nat)
    (counted : reads = slots*passes) (bounded : passes ≤ passBound) :
    reads ≤ slots*passBound := by
  rw [counted]
  exact Nat.mul_le_mul_left slots bounded

theorem primary_threshold_changes : (7 : Nat) ≥ 6+1 ∧ ¬ ((6 : Nat) ≥ 6+1) := by decide

end LocalStreaming
