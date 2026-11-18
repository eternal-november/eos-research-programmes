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
end ContextualJobs
