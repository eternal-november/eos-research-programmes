import Std

/-! Selected acquisition kernels. Physical wiring, schedule realization,
continuing source renewal and the whole-window footprint are separate. -/
namespace LocalAcquisition

def Vote (a b : Option Nat) (p : Nat) : Prop :=
  (∃ v, a = some v ∧ v ≤ p) ∨ (∃ v, b = some v ∧ v ≤ p)

theorem logical_vote_sound (a b : Option Nat) (lower p : Nat)
    (sa : ∀ v, a = some v → lower ≤ v)
    (sb : ∀ v, b = some v → lower ≤ v)
    (vote : Vote a b p) : lower ≤ p := by
  rcases vote with ⟨v, hv, hp⟩ | ⟨v, hv, hp⟩
  · exact Nat.le_trans (sa v hv) hp
  · exact Nat.le_trans (sb v hv) hp

theorem logical_vote_available (a b : Option Nat) (upper p : Nat)
    (sa : ∀ v, a = some v → v ≤ upper)
    (sb : ∀ v, b = some v → v ≤ upper)
    (available : (∃ v, a = some v) ∨ (∃ v, b = some v))
    (large : upper ≤ p) : Vote a b p := by
  rcases available with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨v, hv, Nat.le_trans (sa v hv) large⟩
  · exact Or.inr ⟨v, hv, Nat.le_trans (sb v hv) large⟩

theorem duplicate_is_one_vote (a b : Bool) :
    (if a || b then 1 else 0 : Nat) ≤ 1 := by
  cases a <;> cases b <;> decide

theorem sample_age (sample emitted received consumed S C D E : Int)
    (cache : emitted - sample ≤ S+C)
    (wire : received - emitted ≤ D)
    (receipt : consumed - received ≤ E) :
    consumed - sample ≤ S+C+D+E := by omega

theorem effect_age (sample read effect age tail : Int)
    (current : read-sample ≤ age) (later : effect-read ≤ tail) :
    effect-sample ≤ age+tail := by omega

theorem actual_cut_tail (cut lastReceipt now D cap : Int)
    (last : lastReceipt ≤ cut+D) (expired : cut+D+cap ≤ now) :
    lastReceipt+cap ≤ now := by omega

theorem arbitrary_counter_expires (counter cap ticks : Nat)
    (bounded : counter ≤ cap) (enough : cap ≤ ticks) : counter-ticks = 0 := by omega

theorem post_freeze_sample (sample read frozen age : Int)
    (ageBound : read-sample ≤ age) (waited : frozen+age ≤ read) :
    frozen ≤ sample := by omega

theorem pair_overlap_covers_old_b_new_a (aRead bRead newStart oldEnd span : Int)
    (_ordered : aRead ≤ bRead) (duration : bRead ≤ aRead+span)
    (overlap : newStart+span ≤ oldEnd) :
    newStart ≤ aRead ∨ bRead ≤ oldEnd := by omega

theorem pair_overlap_covers_old_a_new_b (aRead bRead newStart oldEnd : Int)
    (ordered : aRead ≤ bRead) (overlap : newStart ≤ oldEnd) :
    aRead ≤ oldEnd ∨ newStart ≤ bRead := by omega

theorem sequential_miss :
    (0 : Int) < 1 ∧ (1 : Int) < 2 ∧ ¬ ((1 : Int) ≤ 0 ∨ (2 : Int) ≤ 1) := by decide

theorem initialization_plus_publication (power initialized clear first delivered gate : Int)
    (prefixBound : initialized ≤ power+clear)
    (firstBound : first ≤ initialized+delivered)
    (gateBound : power+clear+delivered ≤ gate) : first ≤ gate := by omega

theorem direct_private_budget (banks reads initialized body : Nat)
    (bankBound : banks ≤ 2) (readBound : reads ≤ 13*11)
    (initBound : initialized ≤ 14) (bodyBound : body ≤ 11*(10*13+10)+3) :
    banks*reads ≤ 286 ∧ initialized+body ≤ 1557 := by
  constructor
  · calc banks*reads ≤ 2*reads := Nat.mul_le_mul_right reads bankBound
         _ ≤ 286 := by omega
  · omega

theorem demand_response_bound (start stable sampled emitted arrived request period conversion cache wire : Int)
    (settled : stable ≤ start+request)
    (visited : sampled ≤ stable+period+conversion)
    (published : emitted ≤ sampled+cache)
    (delivered : arrived ≤ emitted+wire) :
    arrived ≤ start+request+period+conversion+cache+wire := by omega

theorem captured_key_mismatch (sampledKey emittedKey wantedKey : Nat)
    (captured : emittedKey = sampledKey) (changed : sampledKey ≠ wantedKey) :
    emittedKey ≠ wantedKey := by omega


/- Expected-value-only writes model actual physical cell transitions, including
failed writes and writes to another cell as unchanged. -/
inductive CellStep (expected : Nat) : Nat → Nat → Prop where
  | unchanged (value : Nat) : CellStep expected value value
  | write (value : Nat) : CellStep expected value expected

inductive CellRun (expected : Nat) : Nat → Nat → Prop where
  | refl (value : Nat) : CellRun expected value value
  | cons {before middle after : Nat} :
      CellStep expected before middle → CellRun expected middle after →
      CellRun expected before after

theorem expected_step_preserves (expected before after : Nat)
    (equal : before = expected) (step : CellStep expected before after) :
    after = expected := by
  cases step with
  | unchanged => exact equal
  | write => rfl

theorem expected_run_preserves (expected before after : Nat)
    (trace : CellRun expected before after) (equal : before = expected) :
    after = expected := by
  induction trace with
  | refl => exact equal
  | cons step tail ih =>
    exact ih (expected_step_preserves _ _ _ equal step)

theorem mutable_match_is_current (cell : Int → Nat)
    (expected : Nat) (entry sample read now age : Int)
    (preserved : ∀ s t, entry ≤ s → s ≤ t → cell s = expected → cell t = expected)
    (sampledBefore : sample ≤ read) (decidedAfter : read ≤ now)
    (ageBound : read-sample ≤ age) (gate : entry+age < read)
    (nominalMatch : cell sample = expected) : cell now = expected := by
  apply preserved sample now
  · omega
  · omega
  · exact nominalMatch

theorem copy_prefix_advance (image intended : Nat → Nat) (cursor : Nat)
    (prior : ∀ j, j < cursor → image j = intended j)
    (current : image cursor = intended cursor) :
    ∀ j, j < cursor+1 → image j = intended j := by
  intro j hj
  by_cases old : j < cursor
  · exact prior j old
  · have atCursor : j = cursor := by omega
    simpa [atCursor] using current

theorem late_wrong_write_violates (wrong : CellStep 1 1 0) : False := by
  cases wrong

theorem mutable_response_bound
    (start requested applied sampled emitted arrived reqDelay writeDelay period conversion cache wire : Int)
    (request : requested ≤ start+reqDelay)
    (write : applied ≤ start+writeDelay)
    (sample : sampled ≤ max requested applied+period+conversion)
    (publish : emitted ≤ sampled+cache)
    (receive : arrived ≤ emitted+wire) :
    arrived ≤ start+max reqDelay writeDelay+period+conversion+cache+wire := by omega


/- Whole-side functional upper certificates. The raw samples' physical error,
variation, time and catalogue coverage instantiate the rowwise hypothesis. -/
def sampleMaximum : List Nat → Nat
  | [] => 0
  | x :: xs => max x (sampleMaximum xs)

theorem member_le_sampleMaximum (xs : List Nat) (x : Nat) (member : x ∈ xs) :
    x ≤ sampleMaximum xs := by
  induction xs with
  | nil => simp at member
  | cons a tail ih =>
    simp only [List.mem_cons] at member
    simp only [sampleMaximum]
    rcases member with equal | rest
    · subst x; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih rest) (Nat.le_max_right _ _)

theorem sampleMaximum_le (xs : List Nat) (bound : Nat)
    (all : ∀ x ∈ xs, x ≤ bound) : sampleMaximum xs ≤ bound := by
  induction xs with
  | nil => simp [sampleMaximum]
  | cons a tail ih =>
    have ha := all a (by simp)
    have ht := ih (fun x hx => all x (by simp [hx]))
    simp only [sampleMaximum]
    omega

theorem conditional_copy_is_maximum (accumulator raw : Nat) :
    (if accumulator < raw then raw else accumulator) = max accumulator raw := by
  split <;> omega

theorem maximum_guard_covers_every_connector (rows : List (Nat × Nat)) (margin limit : Nat)
    (futureEnvelope : ∀ row ∈ rows, row.1 ≤ row.2+margin)
    (guard : sampleMaximum (rows.map Prod.snd)+margin ≤ limit) :
    ∀ row ∈ rows, row.1 ≤ limit := by
  intro row member
  have sampleMember : row.2 ∈ rows.map Prod.snd := List.mem_map.mpr ⟨row, member, rfl⟩
  have below := member_le_sampleMaximum (rows.map Prod.snd) row.2 sampleMember
  have envelope := futureEnvelope row member
  omega

theorem raw_read_age_from_fold (sample completed emitted received compared fold cache wire retention : Int)
    (aggregation : completed-sample ≤ fold)
    (published : emitted-completed ≤ cache)
    (delivered : received-emitted ≤ wire)
    (retained : compared-received ≤ retention) :
    compared-sample ≤ fold+cache+wire+retention := by omega

theorem margin_threshold_safe (reading margin limit : Nat)
    (formed : margin ≤ limit) (passed : reading ≤ limit-margin) :
    reading+margin ≤ limit := by omega

theorem unavailable_does_not_pass (limit margin : Nat) :
    ¬ (limit+1 ≤ limit-margin) := by omega

theorem isolation_deficit_guard (isolation deficit limit scale : Nat)
    (functional : scale ≤ isolation+deficit) (guard : deficit ≤ limit) :
    scale-limit ≤ isolation := by omega


def clipMeasurement (raw cap : Int) : Int :=
  if raw < 0 then 0 else if cap < raw then cap else raw

theorem clipping_preserves_error (truth raw cap error : Int)
    (lower : 0 ≤ truth) (upper : truth ≤ cap) (positiveError : 0 ≤ error)
    (rawLower : raw-error ≤ truth) (rawUpper : truth ≤ raw+error) :
    clipMeasurement raw cap-error ≤ truth ∧ truth ≤ clipMeasurement raw cap+error := by
  unfold clipMeasurement
  split
  · omega
  · split <;> omega

theorem offset_numeric_is_distinct (truth raw cap error bias : Int)
    (lower : 0 ≤ truth) (upper : truth ≤ cap) (biasBound : error < bias)
    (rawLower : raw-error ≤ truth) (rawUpper : truth ≤ raw+error) :
    0 < bias+raw ∧ bias+raw ≤ bias+cap+error := by omega

#print axioms logical_vote_sound
#print axioms logical_vote_available
#print axioms duplicate_is_one_vote
#print axioms sample_age
#print axioms effect_age
#print axioms actual_cut_tail
#print axioms arbitrary_counter_expires
#print axioms post_freeze_sample
#print axioms pair_overlap_covers_old_b_new_a
#print axioms pair_overlap_covers_old_a_new_b
#print axioms sequential_miss
#print axioms initialization_plus_publication
#print axioms direct_private_budget

#print axioms demand_response_bound
#print axioms captured_key_mismatch

#print axioms expected_step_preserves
#print axioms expected_run_preserves
#print axioms mutable_match_is_current
#print axioms copy_prefix_advance
#print axioms late_wrong_write_violates
#print axioms mutable_response_bound

#print axioms member_le_sampleMaximum
#print axioms sampleMaximum_le
#print axioms conditional_copy_is_maximum
#print axioms maximum_guard_covers_every_connector
#print axioms raw_read_age_from_fold
#print axioms margin_threshold_safe
#print axioms unavailable_does_not_pass
#print axioms isolation_deficit_guard

#print axioms clipping_preserves_error
#print axioms offset_numeric_is_distinct

end LocalAcquisition
