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

end LocalAcquisition
