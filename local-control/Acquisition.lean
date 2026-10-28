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

end LocalAcquisition
