import Std

/-! Three-identity synchronous signed broadcast and phase-separated terminal evidence.
The finite message-set semantics is independently realized in digital_model.py.
No cryptographic implementation, arbitrary HotStuff view, or physical effect is encoded. -/
namespace ByzantineControlDigital

abbrev Actor := Fin 3
abbrev Fault := Fin 4 -- 0/1/2: one faulty actor; 3: no faulty actor
abbrev Bits := Bool × Bool

def member (s : Bits) (v : Bool) : Bool := if v then s.2 else s.1
def singleton (v : Bool) : Bits := (!v, v)
def union (s t : Bits) : Bits := (s.1 || t.1, s.2 || t.2)
abbrev subset (s t : Bits) : Prop := (s.1 = true → t.1 = true) ∧ (s.2 = true → t.2 = true)
def choose (s : Bits) : Bool := !s.1 && s.2
abbrev correct (b : Fault) (i : Actor) : Prop := b.val ≠ i.val

structure RoundData where
  input : Bool
  raw1 : Bits
  raw2 : Bits
  echo1 : Bits -- received by actor 1 from actor 2
  echo2 : Bits -- received by actor 2 from actor 1
  deriving DecidableEq

abbrev Legal (b : Fault) (s : RoundData) : Prop :=
  (b.val ≠ 0 → s.raw1 = singleton s.input ∧ s.raw2 = singleton s.input) ∧
  (b.val ≠ 1 → s.echo2 = s.raw1) ∧
  (b.val ≠ 2 → s.echo1 = s.raw2) ∧
  (b.val = 1 → subset s.echo2 (singleton s.input)) ∧
  (b.val = 2 → subset s.echo1 (singleton s.input))

def decision (s : RoundData) (i : Actor) : Bool :=
  if i.val = 0 then s.input else if i.val = 1 then choose (union s.raw1 s.echo1)
  else choose (union s.raw2 s.echo2)

theorem choose_singleton (v : Bool) : choose (singleton v) = v := by cases v <;> decide

theorem union_comm (s t : Bits) : union s t = union t s := by
  rcases s with ⟨a,b⟩; rcases t with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem union_subset_singleton (s : Bits) (v : Bool) (h : subset s (singleton v)) :
    union (singleton v) s = singleton v := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> cases v <;> simp_all [subset, singleton, union]

theorem correct_leader_validity (b : Fault) (s : RoundData) (h : Legal b s)
    (leader : b.val ≠ 0) (i : Actor) : decision s i = s.input := by
  obtain ⟨raw, echo2, echo1, bad1, bad2⟩ := h
  obtain ⟨r1,r2⟩ := raw leader
  have e1 : subset s.echo1 (singleton s.input) := by
    by_cases hb : b.val = 2
    · exact bad2 hb
    · rw [echo1 hb, r2]; exact ⟨id,id⟩
  have e2 : subset s.echo2 (singleton s.input) := by
    by_cases hb : b.val = 1
    · exact bad1 hb
    · rw [echo2 hb, r1]; exact ⟨id,id⟩
  unfold decision
  split
  · rfl
  · split
    · rw [r1, union_subset_singleton _ _ e1, choose_singleton]
    · rw [r2, union_subset_singleton _ _ e2, choose_singleton]

theorem broadcast_agreement (b : Fault) (s : RoundData) (h : Legal b s)
    (i j : Actor) (hi : correct b i) (hj : correct b j) : decision s i = decision s j := by
  by_cases leader : b.val = 0
  · have bi : i.val ≠ 0 := by unfold correct at hi; omega
    have bj : j.val ≠ 0 := by unfold correct at hj; omega
    have h1 : b.val ≠ 1 := by omega
    have h2 : b.val ≠ 2 := by omega
    have e1 := h.2.2.1 h2
    have e2 := h.2.1 h1
    simp only [decision, bi, bj, ↓reduceIte, e1, e2]
    rw [union_comm s.raw2 s.raw1]
    split <;> split <;> rfl
  · exact (correct_leader_validity b s h leader i).trans (correct_leader_validity b s h leader j).symm

def outputAt (s : RoundData) (i : Actor) (phase : Nat) : Option Bool :=
  if phase < 2 then none else some (decision s i)

theorem termination_at_two (s : RoundData) (i : Actor) : outputAt s i 2 = some (decision s i) := by rfl

theorem output_irrevocable (s : RoundData) (i : Actor) (t : Nat) (h : 2 ≤ t) :
    outputAt s i t = outputAt s i 2 := by simp [outputAt]; omega

theorem two_correct (b : Fault) : ∃ i j : Actor, i ≠ j ∧ correct b i ∧ correct b j := by
  revert b
  decide

def Terminal (b : Fault) (s : RoundData) (i : Actor) (v : Bool) : Prop :=
  correct b i → decision s i = v

def Certificate (b : Fault) (s : RoundData) (v : Bool) : Prop :=
  ∃ i j : Actor, i ≠ j ∧ Terminal b s i v ∧ Terminal b s j v

theorem certificate_has_correct (b : Fault) (s : RoundData) (v : Bool)
    (cert : Certificate b s v) : ∃ i, correct b i ∧ decision s i = v := by
  obtain ⟨i,j,neq,ti,tj⟩ := cert
  by_cases hi : correct b i
  · exact ⟨i,hi,ti hi⟩
  · have hj : correct b j := by
      intro hj
      have eqi : b.val = i.val := by simpa [correct] using hi
      exact neq (Fin.ext (eqi.symm.trans hj))
    exact ⟨j,hj,tj hj⟩

theorem certificate_sound (b : Fault) (s : RoundData) (h : Legal b s)
    (v : Bool) (cert : Certificate b s v) (i : Actor) (hi : correct b i) : decision s i = v := by
  obtain ⟨j,hj,dj⟩ := certificate_has_correct b s v cert
  exact (broadcast_agreement b s h i j hi hj).trans dj

theorem certificate_exclusion (b : Fault) (s : RoundData) (h : Legal b s)
    (v w : Bool) (cv : Certificate b s v) (cw : Certificate b s w) : v = w := by
  obtain ⟨i,hi,di⟩ := certificate_has_correct b s v cv
  exact di.symm.trans (certificate_sound b s h w cw i hi)

theorem certificate_available (b : Fault) (s : RoundData) (h : Legal b s) :
    ∃ v i j, i ≠ j ∧ correct b i ∧ correct b j ∧ decision s i = v ∧ decision s j = v := by
  obtain ⟨i,j,neq,hi,hj⟩ := two_correct b
  exact ⟨decision s i,i,j,neq,hi,hj,rfl,broadcast_agreement b s h j i hj hi⟩

/- These are receiver-visible current-epoch, terminal-phase signature tokens.
Their provenance condition concerns signing code, not the desired exclusion conclusion. -/
def HasCertificate (received : Actor → Bool → Prop) (v : Bool) : Prop :=
  ∃ i j, i ≠ j ∧ received i v ∧ received j v

structure ReceiptWorld where
  bad : Fault
  round : RoundData
  legal : Legal bad round
  received : Actor → Bool → Prop
  provenance : ∀ i v, received i v → Terminal bad round i v

theorem receipt_sound (w : ReceiptWorld) (v : Bool) (hc : HasCertificate w.received v) :
    ∀ i, correct w.bad i → decision w.round i = v := by
  obtain ⟨i,j,neq,ri,rj⟩ := hc
  exact certificate_sound w.bad w.round w.legal v
    ⟨i,j,neq,w.provenance i v ri,w.provenance j v rj⟩

/- Universal warrant over all operationally legal worlds with the same bundle.
The full-history knowledge claim follows since equal full views imply equal bundles. -/
theorem receipt_warrants_decision (w : ReceiptWorld) (v : Bool)
    (hc : HasCertificate w.received v) :
    ∀ w' : ReceiptWorld, w'.received = w.received →
      ∀ i, correct w'.bad i → decision w'.round i = v := by
  intro w' eq
  apply receipt_sound w' v
  simpa [eq] using hc

def ledger (rounds : Nat → RoundData) (i : Actor) (completed slot : Nat) : Option Bool :=
  if slot < completed then some (decision (rounds slot) i) else none

theorem ledger_agreement (b : Fault) (rounds : Nat → RoundData)
    (legal : ∀ e, Legal b (rounds e)) (i j : Actor) (hi : correct b i) (hj : correct b j)
    (completed slot : Nat) : ledger rounds i completed slot = ledger rounds j completed slot := by
  unfold ledger
  rw [broadcast_agreement b (rounds slot) (legal slot) i j hi hj]

theorem ledger_append_preserves_history (rounds : Nat → RoundData) (i : Actor)
    (completed slot : Nat) (h : slot < completed) :
    ledger rounds i (completed+1) slot = ledger rounds i completed slot := by
  simp [ledger, h, Nat.lt_succ_of_lt h]

theorem certificate_historical_finality (b : Fault) (rounds : Nat → RoundData)
    (legal : ∀ e, Legal b (rounds e)) (slot completed : Nat) (v : Bool)
    (cert : Certificate b (rounds slot) v) (done : slot < completed) :
    ∀ i, correct b i → ledger rounds i completed slot = some v := by
  intro i hi
  simp [ledger, done, certificate_sound b (rounds slot) (legal slot) v cert i hi]

/- Negative evidence concerns honest first-round receipts, not hidden Byzantine signing. -/
theorem member_union_false (s t : Bits) (v : Bool) (h : member (union s t) v = false) :
    member s v = false ∧ member t v = false := by
  cases v <;> simpa [member, union] using h

theorem absent_after_echo_excludes_honest_receipt (b : Fault) (s : RoundData)
    (h : Legal b s) (i : Actor) (_hi : correct b i) (_follower : i.val ≠ 0)
    (v : Bool)
    (absent : member (if i.val = 1 then union s.raw1 s.echo1 else union s.raw2 s.echo2) v = false)
    (j : Actor) (_hj : correct b j) (_jf : j.val ≠ 0) :
    member (if j.val = 1 then s.raw1 else s.raw2) v = false := by
  by_cases leader : b.val = 0
  · have h1 : b.val ≠ 1 := by omega
    have h2 : b.val ≠ 2 := by omega
    have e1 := h.2.2.1 h2
    have e2 := h.2.1 h1
    by_cases ii : i.val = 1
    · simp only [ii, ↓reduceIte, e1] at absent
      have both := member_union_false s.raw1 s.raw2 v absent
      split <;> simp_all
    · simp only [ii, ↓reduceIte, e2] at absent
      have both := member_union_false s.raw2 s.raw1 v absent
      split <;> simp_all
  · obtain ⟨r1,r2⟩ := h.1 leader
    have rawAbsent : member (singleton s.input) v = false := by
      by_cases ii : i.val = 1
      · simp only [ii, ↓reduceIte] at absent
        simpa [r1] using (member_union_false s.raw1 s.echo1 v absent).1
      · simp only [ii, ↓reduceIte] at absent
        simpa [r2] using (member_union_false s.raw2 s.echo2 v absent).1
    split <;> simpa [r1,r2] using rawAbsent

#print axioms choose_singleton
#print axioms union_comm
#print axioms union_subset_singleton
#print axioms correct_leader_validity
#print axioms broadcast_agreement
#print axioms termination_at_two
#print axioms output_irrevocable
#print axioms two_correct
#print axioms certificate_has_correct
#print axioms certificate_sound
#print axioms certificate_exclusion
#print axioms certificate_available
#print axioms receipt_sound
#print axioms receipt_warrants_decision
#print axioms ledger_agreement
#print axioms ledger_append_preserves_history
#print axioms certificate_historical_finality
#print axioms member_union_false
#print axioms absent_after_echo_excludes_honest_receipt
end ByzantineControlDigital
