import Std

/-!
A window is indexed by one installation, fixed local policy, request and
release cut. Times are elapsed from that cut. A denial and its candidate
envelope are analysis data on one run; a participant need not observe either.
-/
namespace ExclusiveService

def Clear (bundle mask : List α) : Prop :=
  ∀ a ∈ bundle, a ∉ mask

def clearB [DecidableEq α] (bundle mask : List α) : Bool :=
  bundle.all fun a => decide (a ∉ mask)

def covers [DecidableEq α] (bundles masks : List (List α)) : Bool :=
  masks.all fun m => bundles.any fun b => clearB b m

theorem clearB_iff [DecidableEq α] {b m : List α} :
    clearB b m = true ↔ Clear b m := by
  simp [clearB, Clear, List.all_eq_true]

theorem covers_iff [DecidableEq α] {bundles masks : List (List α)} :
    covers bundles masks = true ↔ ∀ m ∈ masks, ∃ b ∈ bundles, Clear b m := by
  simp [covers, List.all_eq_true, List.any_eq_true, clearB_iff]

/-- An envelope transversal. Realization of a losing physical history is
a separate reflection obligation, especially if masks overapproximate denial. -/
theorem failure_iff [DecidableEq α] {bundles masks : List (List α)} :
    covers bundles masks = false ↔
      ∃ m ∈ masks, ∀ b ∈ bundles, ∃ a ∈ b, a ∈ m := by
  classical
  have neg : covers bundles masks = false ↔ ¬ covers bundles masks = true := by
    cases covers bundles masks <;> simp
  rw [neg, covers_iff]
  simp [Clear]

private def chooseBundle [DecidableEq α] (m : List α) :
    (bs : List (List α)) → (∃ b ∈ bs, Clear b m) → {b // b ∈ bs ∧ Clear b m}
  | [], h => by simp at h
  | b :: bs, existsClear =>
    if hb : clearB b m = true then
      ⟨b, List.mem_cons_self, clearB_iff.mp hb⟩
    else
      let rest : ∃ x ∈ bs, Clear x m := by
        obtain ⟨x, hx, clear⟩ := existsClear
        rcases List.mem_cons.mp hx with eq | tail
        · subst x
          exact (hb (clearB_iff.mpr clear)).elim
        · exact ⟨x, tail, clear⟩
      let w := chooseBundle m bs rest
      ⟨w.val, List.mem_cons_of_mem b w.property.1, w.property.2⟩

/-- The adapter supplies semantics for events of this named request. A credit
is an actual new, individually identified useful effect since the opening cut.
Identifying distinct effects by their destination would invalidate that adapter. -/
structure Source (Atom Run Issue Credit : Type) where
  cutoff : Nat
  lag : Nat
  envelope : Run → List Atom
  denied : Run → Atom → Prop
  conservativelyCovered : ∀ h a, denied h a → a ∈ envelope h
  committed : Run → Issue → Prop
  issueTime : Run → Issue → Nat
  earned : Run → Credit → Prop
  creditTime : Run → Credit → Nat
  settlesIssue : Run → Issue → Credit → Prop
  settlement : ∀ h i, committed h i →
    {r // earned h r ∧ settlesIssue h i r ∧ issueTime h i ≤ creditTime h r ∧
      creditTime h r ≤ issueTime h i + lag}

structure Window (Atom Run Issue Credit : Type) extends Source Atom Run Issue Credit where
  bundles : List (List Atom)
  masks : List (List Atom)
  admitted : ∀ h, envelope h ∈ masks
  opportunity : ∀ h b, b ∈ bundles → (∀ a ∈ b, ¬ denied h a) →
    {i // committed h i ∧ issueTime h i ≤ cutoff}

structure Result (w : Window A H I R) (h : H) where
  bundle : List A
  registered : bundle ∈ w.bundles
  available : ∀ a ∈ bundle, ¬ w.denied h a
  issue : I
  committed : w.committed h issue
  timelyIssue : w.issueTime h issue ≤ w.cutoff
  credit : R
  earned : w.earned h credit
  sameIssue : w.settlesIssue h issue credit
  ordered : w.issueTime h issue ≤ w.creditTime h credit
  withinLag : w.creditTime h credit ≤ w.issueTime h issue + w.lag
  timely : w.creditTime h credit ≤ w.cutoff + w.lag
  uniqueOnRun : ∀ r, w.earned h r → r = credit

/-- Construct the analyst's certificate for each supplied run. The policy is
already fixed. In particular the theorem selects no physical action using the mask. -/
def exclusiveBy [DecidableEq A] (w : Window A H I R)
    (checked : covers w.bundles w.masks = true)
    (safe : ∀ h r s, w.earned h r → w.earned h s → r = s)
    (h : H) : Result w h := by
  let b := chooseBundle (w.envelope h) w.bundles
    (covers_iff.mp checked (w.envelope h) (w.admitted h))
  have available : ∀ a ∈ b.val, ¬ w.denied h a :=
    fun a member denied => b.property.2 a member (w.conservativelyCovered h a denied)
  let i := w.opportunity h b.val b.property.1 available
  let r := w.settlement h i.val i.property.1
  exact {
    bundle := b.val, registered := b.property.1, available
    issue := i.val, committed := i.property.1, timelyIssue := i.property.2
    credit := r.val, earned := r.property.1, sameIssue := r.property.2.1
    ordered := r.property.2.2.1, withinLag := r.property.2.2.2
    timely := Nat.le_trans r.property.2.2.2 (Nat.add_le_add_right i.property.2 w.lag)
    uniqueOnRun := fun x hx => safe h x r.val hx r.property.1
  }

private theorem sameOfShort (xs : List R) (short : xs.length ≤ 1)
    {a b : R} (ha : a ∈ xs) (hb : b ∈ xs) : a = b := by
  cases xs with
  | nil => simp at ha
  | cons x rest =>
    cases rest with
    | nil => simp_all
    | cons y tail => simp at short

/-- A conserved integral unit and persistent cumulative receipt identities
give the safety premise across arbitrarily distant cuts of the same run. -/
theorem custodySafety (held : Nat → Nat) (credits : Nat → List R)
    (conserved : ∀ n, held n + (credits n).length = 1)
    (persist : ∀ m n, m ≤ n → ∀ r ∈ credits m, r ∈ credits n)
    {r s : R} (hr : ∃ n, r ∈ credits n) (hs : ∃ n, s ∈ credits n) : r = s := by
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, hj⟩ := hs
  have cur := conserved (max i j)
  exact sameOfShort (credits (max i j)) (by omega)
    (persist i _ (Nat.le_max_left i j) r hi)
    (persist j _ (Nat.le_max_right i j) s hj)

/-- A different safety supplier: distinct committed destinations would need
an honest common voter to endorse both. Each destination also needs a one-shot
effect law, since one endorsement may otherwise be replayed twice there. -/
theorem quorumSafety (earned : R → Prop) (dest : R → D)
    (signed : R → V → Prop) (honest : V → Prop)
    (oneAtDest : ∀ r s, earned r → earned s → dest r = dest s → r = s)
    (overlap : ∀ r s, earned r → earned s → dest r ≠ dest s →
      ∃ v, honest v ∧ signed r v ∧ signed s v)
    (boundVote : ∀ v r s, honest v → signed r v → signed s v → dest r = dest s)
    {r s} (hr : earned r) (hs : earned s) : r = s := by
  apply oneAtDest r s hr hs
  by_cases same : dest r = dest s
  · exact same
  · obtain ⟨v, hv, vr, vs⟩ := overlap r s hr hs same
    exact boundVote v r s hv vr vs

def docks : List (List Nat) := [[0], [1]]
def dockMasks : List (List Nat) := [[], [0], [1]]
theorem dock_cover : covers docks dockMasks = true := by decide
theorem dock_mobile_failure : covers docks (dockMasks ++ [[0, 1]]) = false := by decide

def triples : List (List Nat) := [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]
def voteMasks : List (List Nat) := [[], [0], [1], [2], [3]]
theorem triple_cover : covers triples voteMasks = true := by decide

/-- Two three-voter certificates have a common voter outside any one fixed
exposure. With two persistent exposures, their two common voters may both fail. -/
def protectedOverlap (bundles masks : List (List Nat)) : Bool :=
  masks.all fun m => bundles.all fun b => bundles.all fun c =>
    b.any fun v => decide (v ∈ c ∧ v ∉ m)
theorem triple_overlap : protectedOverlap triples voteMasks = true := by decide
theorem triple_two_denials : covers triples [[0, 1]] = false := by decide
theorem triple_two_overlap_failure : protectedOverlap triples [[0, 1]] = false := by decide

theorem protectedOverlap_iff {bs ms : List (List Nat)} :
    protectedOverlap bs ms = true ↔ ∀ m ∈ ms, ∀ b ∈ bs, ∀ c ∈ bs,
      ∃ v ∈ b, v ∈ c ∧ v ∉ m := by
  simp [protectedOverlap, List.all_eq_true, List.any_eq_true]

/-- The source binds its guards to the actual P discharge and the same load at
Q. A lucky P discharge by a faulty P still counts on that run. -/
structure Carrier (H I R : Type) extends Source Nat H I R where
  maskOnPass : ∀ h, envelope h ∈ dockMasks
  pFired : H → Bool
  loadedAtQ : H → Bool
  pIssue : H → I
  qIssue : H → I
  pActs : ∀ h, ¬ denied h 0 → pFired h = true
  pEffect : ∀ h, pFired h = true →
    committed h (pIssue h) ∧ issueTime h (pIssue h) ≤ cutoff
  carryForward : ∀ h, pFired h = false → loadedAtQ h = true
  qActs : ∀ h, loadedAtQ h = true → ¬ denied h 1 →
    committed h (qIssue h) ∧ issueTime h (qIssue h) ≤ cutoff
  held : H → Nat → Nat
  credits : H → Nat → List R
  conserved : ∀ h t, held h t + (credits h t).length = 1
  persist : ∀ h m n, m ≤ n → ∀ r ∈ credits h m, r ∈ credits h n
  countsActual : ∀ h r, earned h r → ∃ t, r ∈ credits h t

def carrierWindow (s : Carrier H I R) : Window Nat H I R where
  toSource := s.toSource
  bundles := docks
  masks := dockMasks
  admitted := s.maskOnPass
  opportunity := by
    intro h b member available
    if hp : s.pFired h = true then
      exact ⟨s.pIssue h, s.pEffect h hp⟩
    else
      have quiet : s.pFired h = false := by cases hb : s.pFired h <;> simp_all
      have qb : 1 ∈ b := by
        simp [docks] at member
        rcases member with eq | eq <;> subst b
        · exact (hp (s.pActs h (available 0 (by simp)))).elim
        · simp
      exact ⟨s.qIssue h, s.qActs h (s.carryForward h quiet) (available 1 qb)⟩

def carrierResult (s : Carrier H I R) (h : H) : Result (carrierWindow s) h :=
  exclusiveBy (carrierWindow s) dock_cover
    (fun run r t hr ht =>
      custodySafety (s.held run) (s.credits run) (s.conserved run) (s.persist run)
        (s.countsActual run r hr) (s.countsActual run t ht)) h

def roster : List Nat := [0, 1, 2, 3]

theorem tripleLayout {b : List Nat} (member : b ∈ triples) :
    b.Sublist roster ∧ b.length = 3 := by
  simp [triples] at member
  rcases member with h | h | h | h <;> subst b <;> decide

/-- Each unblocked signer contributes its own counted ballot for the same
proposal. Duplicating one signer's message cannot fill a new roster position. -/
theorem threeCount (ballot : Nat → Bool) {b : List Nat} (member : b ∈ triples)
    (good : ∀ v ∈ b, ballot v = true) : 3 ≤ (roster.filter ballot).length := by
  obtain ⟨sub, size⟩ := tripleLayout member
  have count := (sub.filter ballot).length_le
  rwa [List.filter_eq_self.mpr good, size] at count

/-- Vote acceptance and actuation are different source facts: honest views
and bounded delivery populate the correct proposal's physical ballot bank,
and a funded threshold trigger can consume its three distinct inputs. -/
structure Quorum (H I R D : Type) extends Source Nat H I R where
  fixedExposure : ∀ h, envelope h ∈ voteMasks
  selected : H → D
  chosenIssue : H → I
  correctBallot : H → Nat → Bool
  honestBallot : ∀ h v, v ∈ roster → ¬ denied h v → correctBallot h v = true
  threshold : ∀ h, 3 ≤ (roster.filter (correctBallot h)).length →
    committed h (chosenIssue h) ∧ issueTime h (chosenIssue h) ≤ cutoff
  destination : H → R → D
  correctReceipt : ∀ h r, settlesIssue h (chosenIssue h) r → destination h r = selected h
  signers : H → R → List Nat
  certificate : ∀ h r, earned h r → signers h r ∈ triples
  boundVote : ∀ h v r t, v ∉ envelope h → v ∈ signers h r → v ∈ signers h t →
    destination h r = destination h t
  oneAtDest : ∀ h r t, earned h r → earned h t → destination h r = destination h t → r = t

def quorumWindow (s : Quorum H I R D) : Window Nat H I R where
  toSource := s.toSource
  bundles := triples
  masks := voteMasks
  admitted := s.fixedExposure
  opportunity h b member available :=
    ⟨s.chosenIssue h, s.threshold h (threeCount (s.correctBallot h) member (by
        intro v hv
        exact s.honestBallot h v ((tripleLayout member).1.subset hv) (available v hv)))⟩

def quorumResult (s : Quorum H I R D) (h : H) : Result (quorumWindow s) h :=
  exclusiveBy (quorumWindow s) triple_cover (fun run r t hr ht =>
    quorumSafety (s.earned run) (s.destination run) (fun x v => v ∈ s.signers run x)
      (fun v => v ∉ s.envelope run) (s.oneAtDest run)
      (fun x y hx hy _ => by
        obtain ⟨v, vx, vy, vh⟩ := protectedOverlap_iff.mp triple_overlap _
          (s.fixedExposure run) _ (s.certificate run x hx) _ (s.certificate run y hy)
        exact ⟨v, vh, vx, vy⟩)
      (s.boundVote run) hr ht) h

theorem quorumCorrect (s : Quorum H I R D) (h : H) :
    s.destination h (quorumResult s h).credit = s.selected h :=
  s.correctReceipt h _ (quorumResult s h).sameIssue

#print axioms exclusiveBy
#print axioms failure_iff
#print axioms custodySafety
#print axioms quorumSafety
#print axioms carrierResult
#print axioms quorumResult
#print axioms quorumCorrect

end ExclusiveService
