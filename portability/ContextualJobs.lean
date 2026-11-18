import Std

/-! Compose bounded local jobs at actual positions of one execution.
The choice of execution and the interpretation of clock and resource bounds
are parameters. A raw interruption returns its witness to the caller.
-/
namespace ContextualJobs

universe u v w

/-- `within i j n` includes causal order on the chosen execution and a
    physical time bound. Natural budgets count units of a common upper-bound
    scale; positions (including their real times) need not be discrete. -/
structure BudgetClock (P : Type u) where
  within : P → P → Nat → Prop
  now : ∀ i, within i i 0
  append : ∀ {i j k m n}, within i j m → within j k n → within i k (m + n)

/-- Closing an obligation and transferring it to another still-charged
    footprint require different, caller-specified certificates. -/
inductive Disposition {P : Type u} (Closed : P → Type v) (Charged : P → Type w) (p : P)
  | closed : Closed p → Disposition Closed Charged p
  | charged : Charged p → Disposition Closed Charged p

structure Arrival {P : Type u} (clock : BudgetClock P)
    (Result : P → Type v) (start : P) (budget : Nat) where
  point : P
  elapsed : Nat
  fits : elapsed ≤ budget
  sameRun : clock.within start point elapsed
  result : Result point

/-- An individual edge can finish, report a particular interruption, or
    make verified progress on this very execution. It cannot select another
    favorable run through the same abstract phase. -/
inductive Local {P : Type u} (clock : BudgetClock P)
    (Closed : P → Type v) (Charged : P → Type w)
    (rank remaining : P → Nat) (start : P) where
  | terminal : Closed start → Local clock Closed Charged rank remaining start
  | interrupted (p : P) (cost : Nat) : clock.within start p cost →
      cost ≤ remaining start → Charged p → Local clock Closed Charged rank remaining start
  | advance (p : P) (cost : Nat) : clock.within start p cost →
      rank p < rank start → cost + remaining p ≤ remaining start →
      Local clock Closed Charged rank remaining start

def closeOnRun {P : Type u} (clock : BudgetClock P)
    (Closed : P → Type v) (Charged : P → Type w) (rank remaining : P → Nat)
    (localStep : (i : P) → Local clock Closed Charged rank remaining i) (start : P) :
    Arrival clock (Disposition Closed Charged) start (remaining start) :=
  match localStep start with
  | .terminal cert => ⟨start, 0, Nat.zero_le _, clock.now start, .closed cert⟩
  | .interrupted p cost same fits cert => ⟨p, cost, fits, same, .charged cert⟩
  | .advance p cost same _smaller fits =>
      let later := closeOnRun clock Closed Charged rank remaining localStep p
      ⟨later.point, cost + later.elapsed,
        Nat.le_trans (Nat.add_le_add_left later.fits cost) fits,
        clock.append same later.sameRun, later.result⟩
termination_by rank start

/-- A rank-free sequencing rule: after the first return, run the next
    operation on its actual returned capability; propagate an interruption
    directly, without erasing its footprint or calling the continuation. -/
def bindOrCharge {P : Type u} {clock : BudgetClock P}
    {Ready Done : P → Type v} {Charge : P → Type w}
    {i : P} {a b : Nat}
    (first : Arrival clock (Disposition Ready Charge) i a)
    (next : (j : P) → Ready j → Arrival clock (Disposition Done Charge) j b) :
    Arrival clock (Disposition Done Charge) i (a+b) :=
  match first.result with
  | .charged cert =>
      ⟨first.point, first.elapsed, Nat.le_trans first.fits (Nat.le_add_right a b),
       first.sameRun, .charged cert⟩
  | .closed ready =>
      let r := next first.point ready
      ⟨r.point, first.elapsed + r.elapsed, Nat.add_le_add first.fits r.fits,
       clock.append first.sameRun r.sameRun, r.result⟩

/-- Sum of the individual bounds for the remaining scheduled stages. -/
def stageBudget (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => cost n + stageBudget cost n

/-- Build a bounded itinerary from consecutive physical stage receipts.
    The index is a proof cursor; an actor need not observe the global stage.
    Evidence for the next stage can retain earlier cuts and live children. -/
def stagesOnRun {P : Type u} (clock : BudgetClock P)
    (Stage : Nat → P → Type v) (Charge : P → Type w) (cost : Nat → Nat)
    (perform : (n : Nat) → (i : P) → Stage (n+1) i →
      Arrival clock (Disposition (Stage n) Charge) i (cost n)) :
    (n : Nat) → (i : P) → Stage n i →
      Arrival clock (Disposition (Stage 0) Charge) i (stageBudget cost n)
  | 0, i, done => ⟨i, 0, Nat.le_refl _, clock.now i, .closed done⟩
  | n+1, i, entry =>
      bindOrCharge (perform n i entry)
        (fun j ready => stagesOnRun clock Stage Charge cost perform n j ready)

/-- Join two already certified results on a common ordered trace segment.
    Each certificate must persist to the later point. This is a maximum
    of two actual arrival times, with no assumption about independent clocks. -/
def joinPersistent {P : Type u} {clock : BudgetClock P}
    (precedes : P → P → Prop) [DecidableRel precedes]
    (total : ∀ p q, precedes p q ∨ precedes q p)
    {A : P → Type v} {B : P → Type w} {i : P} {a b : Nat}
    (left : Arrival clock A i a) (right : Arrival clock B i b)
    (carryLeft : ∀ p q, precedes p q → A p → A q)
    (carryRight : ∀ p q, precedes p q → B p → B q) :
    Arrival clock (fun p => A p × B p) i (max a b) :=
  if order : precedes left.point right.point then
    ⟨right.point, right.elapsed, Nat.le_trans right.fits (Nat.le_max_right _ _),
     right.sameRun, (carryLeft _ _ order left.result, right.result)⟩
  else
    let later := (total left.point right.point).resolve_left order
    ⟨left.point, left.elapsed, Nat.le_trans left.fits (Nat.le_max_left _ _),
     left.sameRun, (left.result, carryRight _ _ later right.result)⟩

/-- Remaining symbols of the active old claim followed by old queued
    claims. Fresh arrivals behind this fixed prefix do not alter the list. -/
inductive OldTxStep : List Nat → List Nat → Prop
  | more (k : Nat) (tail : List Nat) : OldTxStep ((k+2)::tail) ((k+1)::tail)
  | last (tail : List Nat) : OldTxStep (1::tail) tail
  | drop (k : Nat) (tail : List Nat) : OldTxStep ((k+1)::tail) tail

theorem oldTxDecrease {a b : List Nat} (event : OldTxStep a b) :
    1 + b.sum ≤ a.sum := by
  cases event <;> simp [List.sum_cons] <;> omega

/-- An actual next service opportunity, including an interruptible source.
    The unit interval is the maximum spacing of usable old-claim edges. -/
inductive TxOpportunity {P : Type u} (clock : BudgetClock P)
    (old : P → List Nat) (Interrupted : P → Type w) (i : P) where
  | service (j : P) : clock.within i j 1 → OldTxStep (old i) (old j) →
      TxOpportunity clock old Interrupted i
  | interrupt (j : P) : clock.within i j 1 → Interrupted j →
      TxOpportunity clock old Interrupted i

def oldQueueDrain {P : Type u} (clock : BudgetClock P)
    (old : P → List Nat) (Interrupted : P → Type w)
    (positive : ∀ i, old i ≠ [] → 0 < (old i).sum)
    (opportunity : (i : P) → old i ≠ [] → TxOpportunity clock old Interrupted i)
    (i : P) :
    Arrival clock (Disposition (fun j => PLift (old j = [])) Interrupted) i (old i).sum :=
  closeOnRun clock _ _ (fun j => (old j).sum) (fun j => (old j).sum)
    (fun j =>
      if empty : old j = [] then .terminal ⟨empty⟩ else
        match opportunity j empty with
        | .interrupt k time evidence => .interrupted k 1 time (positive j empty) evidence
        | .service k time event =>
          have reduces := oldTxDecrease event
          .advance k 1 time (by omega) reduces) i

#print axioms oldTxDecrease
#print axioms oldQueueDrain
#print axioms stagesOnRun
#print axioms joinPersistent
#print axioms closeOnRun
#print axioms bindOrCharge
/-- For a first-defect proof, request a step only at a point already reached
    from this job's start with enough of its original budget remaining. -/
def closeInBudget {P : Type u} (clock : BudgetClock P)
    (Closed : P → Type v) (Charged : P → Type w) (rank remaining : P → Nat) (start : P)
    (step : (i : P) → (used : Nat) → clock.within start i used →
      used + remaining i ≤ remaining start → Local clock Closed Charged rank remaining i) :
    Arrival clock (Disposition Closed Charged) start (remaining start) :=
  let rec go (i : P) (used : Nat) (before : clock.within start i used)
      (room : used + remaining i ≤ remaining start) :
      Arrival clock (Disposition Closed Charged) i (remaining i) :=
    match step i used before room with
    | .terminal cert => ⟨i,0,Nat.zero_le _,clock.now i,.closed cert⟩
    | .interrupted p cost same fits cert => ⟨p,cost,fits,same,.charged cert⟩
    | .advance p cost same _smaller fits =>
      let later := go p (used+cost) (clock.append before same) (by omega)
      ⟨later.point,cost+later.elapsed,
        Nat.le_trans (Nat.add_le_add_left later.fits cost) fits,
        clock.append same later.sameRun,later.result⟩
  termination_by rank i
  go start 0 (clock.now start) (by omega)

#print axioms closeInBudget

/-- Open the obligation at a consumer's demand, before an attempted issue.
    A lawful abstention or fallback belongs in Done when the source contract
    permits it. A genuinely missing terminal yields the particular blocking
    receipt on this same bounded run, even if no command was ever emitted. -/
def explainMiss {P : Type u} (clock : BudgetClock P)
    (Done : P → Type v) (Stopped : P → Type w) (rank remaining : P → Nat)
    (demand : P)
    (step : (i : P) → (used : Nat) → clock.within demand i used →
      used + remaining i ≤ remaining demand → Local clock Done Stopped rank remaining i)
    (missing : ∀ j cost, clock.within demand j cost →
      cost ≤ remaining demand → Done j → False) :
    Arrival clock Stopped demand (remaining demand) := by
  let arrival := closeInBudget clock Done Stopped rank remaining demand step
  cases arrival.result with
  | closed terminal =>
    exact False.elim (missing _ _ arrival.sameRun arrival.fits terminal)
  | charged actual =>
    exact ⟨arrival.point,arrival.elapsed,arrival.fits,arrival.sameRun,actual⟩

#print axioms explainMiss

namespace Handoff

/-- Order is physical causal order, including microsteps at the same time.
    The common unit bounds elapsed time; event times need not be integral. -/
structure WindowOrder (clock : BudgetClock Nat) where
  forward : ∀ a b n, clock.within a b n → a ≤ b
  subinterval : ∀ {a b c d n}, a ≤ b → b ≤ c → c ≤ d →
    clock.within a d n → clock.within b c n
  widen : ∀ {a b m n}, m ≤ n → clock.within a b m → clock.within a b n

/-- A sponsor too far before the old-bank loss for BOTH formation and the
    demand window forces every reachable formation step into the strict past
    of the demand. Nothing here assumes that the replacement actually formed. -/
theorem strictSponsor {clock : BudgetClock Nat} (ord : WindowOrder clock)
    {trigger loss start finish budget width j used : Nat}
    (triggerBefore : trigger ≤ loss) (lossBy : loss ≤ finish)
    (window : clock.within start finish width)
    (separated : ¬ clock.within trigger loss (budget + width))
    (reached : clock.within trigger j used) (fits : used ≤ budget) :
    j < start ∧ j < loss := by
  have withinBudget := ord.widen fits reached
  have beforeLoss : j < loss := by
    by_cases late : loss ≤ j
    · have bound := ord.subinterval (Nat.le_refl trigger) triggerBefore late withinBudget
      exact False.elim (separated (ord.widen (Nat.le_add_right budget width) bound))
    · omega
  constructor
  · by_cases late : start ≤ j
    · have tail := ord.subinterval late (Nat.le_of_lt beforeLoss) lossBy window
      exact False.elim (separated (clock.append withinBudget tail))
    · omega
  · exact beforeLoss

/-- One actual incarnation and its usability evidence at every queried cut.
    Birth here is the beginning of the witnessed service interval. -/
structure Held {Bank : Type u} (Ready : Bank → Nat → Type v) (start through : Nat) where
  bank : Bank
  since : Nat
  byStart : since ≤ start
  byEnd : since ≤ through
  readAt : ∀ j, since ≤ j → j ≤ through → Ready bank j

def carryTo {A : Nat → Type v} {fromCut toCut : Nat} (entry : A fromCut)
    (advance : ∀ k, fromCut ≤ k → k < toCut → A k → A (k+1)) :
    (j : Nat) → fromCut ≤ j → j ≤ toCut → A j
  | 0, after, _ => by
    have eq : fromCut = 0 := by omega
    exact eq ▸ entry
  | k+1, after, before => by
    by_cases eq : fromCut = k+1
    · exact eq ▸ entry
    · exact advance k (by omega) (by omega) (carryTo entry advance k (by omega) (by omega))

/-- Failure evidence retains the actual local job, its trigger, deadline
    budget and interruption point. Its projection into a raw cover is checked
    by its caller, including the reach of the original uncompleted work. -/
structure Interruption {clock : BudgetClock Nat} (Stop : Nat → Type w) (start : Nat) where
  trigger : Nat
  budget : Nat
  receipt : Arrival clock Stop trigger budget
  beforeStart : receipt.point < start

def prepareReplacement {Bank : Type u} {clock : BudgetClock Nat} (ord : WindowOrder clock)
    (Ready : Bank → Nat → Type v) (Stop : Nat → Type w)
    (bank : Bank) (trigger loss start finish width : Nat)
    (triggerBefore : trigger ≤ loss) (lossBy : loss ≤ finish)
    (window : clock.within start finish width) (rank remaining : Nat → Nat)
    (separated : ¬ clock.within trigger loss (remaining trigger + width))
    (step : ∀ i used, clock.within trigger i used → used + remaining i ≤ remaining trigger →
      i < start → Local clock (Ready bank) Stop rank remaining i)
    (retain : ∀ k, trigger ≤ k → k < loss → Ready bank k → Ready bank (k+1)) :
    Held Ready start loss ⊕ Interruption (clock := clock) Stop start := by
  let result := closeInBudget clock (Ready bank) Stop rank remaining trigger
    (fun i used reached room => step i used reached room
      (strictSponsor ord triggerBefore lossBy window separated reached (by omega)).1)
  have early := strictSponsor ord triggerBefore lossBy window separated result.sameRun result.fits
  cases result.result with
  | closed ready =>
    exact .inl ⟨bank,result.point,Nat.le_of_lt early.1,Nat.le_of_lt early.2,
      carryTo ready (fun k h₁ h₂ => retain k
        (Nat.le_trans (ord.forward _ _ _ result.sameRun) h₁) h₂)⟩
  | charged receipt =>
    exact .inr ⟨trigger,remaining trigger,
      ⟨result.point,result.elapsed,result.fits,result.sameRun,receipt⟩,early.1⟩

/-- Seek the last structural loss since an established entry, then frame that
    single incarnation over the remaining suffix. At each step the loss flag
    belongs to the analyst's actual event trace, not to the local selector. -/
def wholeWindow {Bank : Type u} {Ready : Bank → Nat → Type v} {Obstruction : Type w}
    (base start finish : Nat) (begun : base ≤ start) (ordered : start ≤ finish)
    (incumbent : Bank) (entry : Ready incumbent base) (loss : Nat → Bool)
    (frame : ∀ k, base ≤ k → k < finish → loss k = false →
      ∀ b, Ready b k → Ready b (k+1))
    (replacement : ∀ k, base ≤ k → k < finish → loss k = true →
      Held Ready start (k+1) ⊕ Obstruction) : Held Ready start finish ⊕ Obstruction := by
  let rec scan (n : Nat) (bounded : base+n ≤ finish) : Held Ready start (base+n) ⊕ Obstruction :=
    match n with
    | 0 => .inl ⟨incumbent,base,begun,by omega, fun j lo hi =>
        (show base = j by omega) ▸ entry⟩
    | m+1 =>
      if h : loss (base+m) = true then
        replacement (base+m) (by omega) (by omega) h
      else
        match scan m (by omega) with
        | .inr cause => .inr cause
        | .inl prev => .inl ⟨prev.bank,prev.since,prev.byStart,by have := prev.byEnd; omega,
            fun j lo hi => by
              by_cases current : j = base+m+1
              · subst j
                exact frame (base+m) (by omega) (by omega) (by simpa using h)
                  prev.bank (prev.readAt _ prev.byEnd (Nat.le_refl _))
              · exact prev.readAt j lo (by omega)⟩
  have eq : base+(finish-base) = finish := by omega
  exact eq ▸ scan (finish-base) (by omega)

/-- The source classifies an actual loss as an interruption, or supplies its
    physical antecedent and the primitive steps of a named replacement. The
    latter may itself be interrupted; it cannot assume a successful handoff. -/
structure Sponsor {Bank : Type u} (clock : BudgetClock Nat)
    (Ready : Bank → Nat → Type v) (Stop : Nat → Type w) (start loss width : Nat) where
  bank : Bank
  trigger : Nat
  triggerBefore : trigger ≤ loss
  rank : Nat → Nat
  remaining : Nat → Nat
  separated : ¬ clock.within trigger loss (remaining trigger + width)
  step : ∀ i used, clock.within trigger i used → used + remaining i ≤ remaining trigger →
    i < start → Local clock (Ready bank) Stop rank remaining i
  retain : ∀ k, trigger ≤ k → k < loss → Ready bank k → Ready bank (k+1)

inductive Failure {clock : BudgetClock Nat} (Stop : Nat → Type w) (start : Nat) where
  | lostAt (post : Nat) : Stop post → Failure Stop start
  | interrupted : Interruption (clock := clock) Stop start → Failure Stop start

def sponsoredWindow {Bank : Type u} {clock : BudgetClock Nat} (ord : WindowOrder clock)
    (Ready : Bank → Nat → Type v) (Stop : Nat → Type w)
    (base start finish width : Nat) (begun : base ≤ start)
    (window : clock.within start finish width) (incumbent : Bank) (entry : Ready incumbent base)
    (loss : Nat → Bool)
    (frame : ∀ k, base ≤ k → k < finish → loss k = false →
      ∀ b, Ready b k → Ready b (k+1))
    (explain : ∀ k, base ≤ k → k < finish → loss k = true →
      Sponsor clock Ready Stop start (k+1) width ⊕ Stop (k+1)) :
    Held Ready start finish ⊕ Failure (clock := clock) Stop start :=
  wholeWindow base start finish begun (ord.forward _ _ _ window) incumbent entry loss frame
    (fun k reached byEnd actual =>
      match explain k reached byEnd actual with
      | .inr cause => .inr (.lostAt (k+1) cause)
      | .inl h =>
        match prepareReplacement ord Ready Stop h.bank h.trigger (k+1) start finish width
            h.triggerBefore byEnd window h.rank h.remaining h.separated h.step h.retain with
        | .inl held => .inl held
        | .inr why => .inr (.interrupted why))

#print axioms sponsoredWindow

#print axioms strictSponsor
#print axioms prepareReplacement
#print axioms wholeWindow
end Handoff

namespace Authority

/-- One actual route along which the same consequential authority survives.
    A legitimate response depending on old data need not carry that authority. -/
inductive Line {C : Nat → Type u} (keeps : (k : Nat) → C k → C (k+1) → Prop)
    {r : Nat} (a : C r) : (n : Nat) → C n → Prop where
  | root : Line keeps a r a
  | carry {k : Nat} {b : C k} {c : C (k+1)} :
      Line keeps a k b → keeps k b c → Line keeps a (k+1) c

theorem lineOrder {C : Nat → Type u} {keeps : (k : Nat) → C k → C (k+1) → Prop}
    {r n : Nat} {a : C r} {b : C n} (line : Line keeps a n b) : r ≤ n := by
  induction line with
  | root => exact Nat.le_refl _
  | carry _ _ earlier => exact Nat.le_trans earlier (Nat.le_succ _)

theorem crossesCut {C : Nat → Type u} {keeps : (k : Nat) → C k → C (k+1) → Prop}
    {r n : Nat} {a : C r} {b : C n} (line : Line keeps a n b)
    (j : Nat) (after : r ≤ j) (before : j ≤ n) : ∃ x : C j, Line keeps a j x := by
  induction line with
  | root =>
    have eq : j = r := by omega
    subst j
    exact ⟨a, .root⟩
  | @carry k x y past step ih =>
    by_cases h : j ≤ k
    · exact ih h
    · have eq : j = k+1 := by omega
      subst j
      exact ⟨y, .carry past step⟩

theorem carryMark {C : Nat → Type u} {keeps : (k : Nat) → C k → C (k+1) → Prop}
    {r n : Nat} {a : C r} {b : C n} (line : Line keeps a n b)
    (mark : (k : Nat) → C k → Prop) (born : mark r a)
    (preserve : ∀ k x y, keeps k x y → mark k x → mark (k+1) y) : mark n b := by
  induction line with
  | root => exact born
  | carry _ step ih => exact preserve _ _ _ step ih

inductive SourceOrParent {C : Nat → Type u} (Seed : (k : Nat) → C k → Type v)
    (keeps : (k : Nat) → C k → C (k+1) → Prop) (n : Nat) (out : C (n+1)) where
  | source : Seed (n+1) out → SourceOrParent Seed keeps n out
  | parent (old : C n) : keeps n old out → SourceOrParent Seed keeps n out

/-- The source occurrence, local receipt and actual chain are recoverable.
    A split or a fanout is traced separately for each consumed liability. -/
def traceRoot {C : Nat → Type u} {Seed : (k : Nat) → C k → Type v}
    {keeps : (k : Nat) → C k → C (k+1) → Prop}
    (initial : (a : C 0) → Seed 0 a)
    (step : (n : Nat) → (b : C (n+1)) → SourceOrParent Seed keeps n b) :
    (n : Nat) → (b : C n) → Σ r, Σ a : C r, Seed r a × PLift (Line keeps a n b)
  | 0, b => ⟨0,b,initial b,⟨.root⟩⟩
  | n+1, b =>
    match step n b with
    | .source witness => ⟨n+1,b,witness,⟨.root⟩⟩
    | .parent old edge =>
      let ⟨r,a,witness,line⟩ := traceRoot initial step n old
      ⟨r,a,witness,⟨.carry line.down edge⟩⟩

/-- Data for a particular expired receipt. A local mark over possible carriers
    is propagated on ordinary retention edges. A bounded job on this run
    excludes that mark at ONE actual cut, including dormant rearming powers.
    The adapter must construct the job for this liability and this consumer. -/
structure Retirement {C : Nat → Type u} (keeps : (k : Nat) → C k → C (k+1) → Prop)
    (clock : BudgetClock Nat) {r : Nat} (a : C r) (challenge : Nat) where
  mark : (k : Nat) → C k → Prop
  born : mark r a
  carry : ∀ k x y, keeps k x y → mark k x → mark (k+1) y
  start : Nat
  afterBirth : r ≤ start
  budget : Nat
  job : Arrival clock (fun j => PLift (∀ x, ¬ mark j x)) start budget
  fitsPrefix : ∀ j cost, clock.within start j cost → cost ≤ budget → j ≤ challenge

theorem excludesLine {C : Nat → Type u} {keeps : (k : Nat) → C k → C (k+1) → Prop}
    {clock : BudgetClock Nat} (forward : ∀ i j cost, clock.within i j cost → i ≤ j)
    {r n : Nat} {a : C r} {b : C n} (fence : Retirement keeps clock a n) :
    ¬ Line keeps a n b := by
  intro line
  have after := Nat.le_trans fence.afterBirth (forward _ _ _ fence.job.sameRun)
  have before := fence.fitsPrefix _ _ fence.job.sameRun fence.job.fits
  obtain ⟨x,past⟩ := crossesCut line _ after before
  exact fence.job.result.down x (carryMark past fence.mark fence.born fence.carry)

/-- Obtain the *particular* still-covered origin and its physical footprint.
    Cover membership needs only logical stability. The computed owner comes from the causal receipts.
    The caller may build each fence under a strictly earlier prefix. -/
def coveredOrigin {C : Nat → Type u} {Seed : (k : Nat) → C k → Type v}
    {keeps : (k : Nat) → C k → C (k+1) → Prop} {T S : Type w}
    (clock : BudgetClock Nat) (forward : ∀ i j cost, clock.within i j cost → i ≤ j)
    (initial : (a : C 0) → Seed 0 a)
    (step : (i : Nat) → (c : C (i+1)) → SourceOrParent Seed keeps i c)
    (owner : {k : Nat} → {a : C k} → Seed k a → T)
    (covered : T → Nat → Prop)
    (stable : ∀ t i, (¬ ¬ covered t i) → covered t i)
    (reach : (i : Nat) → C i → S → Prop) (footprint : T → S → Prop)
    (originReach : ∀ {i a} (s : Seed i a) q, reach i a q → footprint (owner s) q)
    (keepReach : ∀ k x y, keeps k x y → ∀ q, reach (k+1) y q → reach k x q)
    (n : Nat) (effect : C n) (q : S) (applies : reach n effect q)
    (retire : ∀ {r a} (s : Seed r a), r ≤ n → ¬ covered (owner s) n → Retirement keeps clock a n) :
    {t : T // covered t n ∧ footprint t q} := by
  obtain ⟨r,a,s,⟨line⟩⟩ := traceRoot initial step n effect
  have active := stable (owner s) n (fun absent =>
    excludesLine forward (retire s (lineOrder line) absent) line)
  have pull : ∀ {j} {x : C j}, Line keeps a j x → reach j x q → reach r a q := by
    intro j x h
    induction h with
    | root => exact id
    | carry _ hop ih => exact fun hx => ih (keepReach _ _ _ hop q hx)
  exact ⟨owner s,active,originReach s q (pull line applies)⟩

/-- A source realization for one named physical query, new TX from an old FIFO
    claim. A charged interruption can close this owner's route only on evidence
    that every surviving liability has been reattributed at that event. Flight,
    parser and receiver authority have other marks and their own clearance. -/
def oldTxRetirement {C : Nat → Type u} {keeps : (k : Nat) → C k → C (k+1) → Prop}
    (clock : BudgetClock Nat) {r n : Nat} (a : C r)
    (mark : (k : Nat) → C k → Prop) (born : mark r a)
    (carry : ∀ k x y, keeps k x y → mark k x → mark (k+1) y)
    (old : Nat → List Nat) (Interrupt : Nat → Type w)
    (positive : ∀ i, old i ≠ [] → 0 < (old i).sum)
    (start : Nat) (afterBirth : r ≤ start)
    (opportunity : (i used : Nat) → clock.within start i used →
      used + (old i).sum ≤ (old start).sum → old i ≠ [] → TxOpportunity clock old Interrupt i)
    (emptyClears : ∀ j, old j = [] → ∀ x, ¬ mark j x)
    (transfer : ∀ j, Interrupt j → ∀ x, ¬ mark j x)
    (margin : ∀ j cost, clock.within start j cost → cost ≤ (old start).sum → j ≤ n) :
    Retirement keeps clock a n := by
  let result := closeInBudget clock (fun j => PLift (old j = [])) Interrupt
    (fun j => (old j).sum) (fun j => (old j).sum) start (fun j used before room =>
      if empty : old j = [] then .terminal ⟨empty⟩ else
        match opportunity j used before room empty with
        | .interrupt k time receipt => .interrupted k 1 time (positive j empty) receipt
        | .service k time event =>
          have smaller := oldTxDecrease event
          .advance k 1 time (by omega) smaller)
  have clear : ∀ x, ¬ mark result.point x := by
    cases result.result with
    | closed h => exact emptyClears _ h.down
    | charged receipt => exact transfer _ receipt
  exact ⟨mark,born,carry,start,afterBirth,(old start).sum,
    ⟨result.point,result.elapsed,result.fits,result.sameRun,⟨clear⟩⟩,margin⟩

/-- Every failed support judgment, including the failure of a required action
    to occur, must actually expose a liability. This composes that local
    source decoder with the covered-origin theorem at the same cut. -/
def supportForViolation {C S T : Type u} (Bad : S → Type v)
    (reach : C → S → Prop) (covered : T → Prop) (footprint : T → S → Prop)
    (expose : (q : S) → Bad q → Σ e : C, PLift (reach e q))
    (locate : (e : C) → (q : S) → reach e q → {t : T // covered t ∧ footprint t q})
    (q : S) (violation : Bad q) : {t : T // covered t ∧ footprint t q} :=
  let ⟨effect,witness⟩ := expose q violation
  locate effect q witness.down

#print axioms supportForViolation
#print axioms oldTxRetirement
#print axioms traceRoot
#print axioms crossesCut
#print axioms excludesLine
#print axioms coveredOrigin
end Authority

end ContextualJobs
