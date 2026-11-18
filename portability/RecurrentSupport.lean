import ContextualJobs

/-! Effective support on one actual run. Operation types, their physical
    entry cuts, the local prescription and the observed outcome tags belong
    to the fixed source interpretation. Proof-time support is supplied later. -/
namespace RecurrentSupport
open ContextualJobs

inductive Form where
  | terminal
  | stopped (atCut cost : Nat)
  | advance (atCut cost : Nat)
  deriving DecidableEq

def Form.endpoint (i : Nat) : Form → Nat
  | .terminal => i
  | .stopped j _ | .advance j _ => j

def form {P : Type} (cut : P → Nat) {clock : BudgetClock P} {Done Stop : P → Type}
    {rank remaining : P → Nat} {i : P} :
    Local clock Done Stop rank remaining i → Form
  | .terminal _ => .terminal
  | .interrupted j c _ _ _ => .stopped (cut j) c
  | .advance j c _ _ _ => .advance (cut j) c

def cursorFollows {P : Type} {clock : BudgetClock P} {Done Stop : P → Type}
    {rank remaining : P → Nat} {i : P} (actual : P → P → Prop) :
    Local clock Done Stop rank remaining i → Prop
  | .terminal _ => True
  | .interrupted j _ _ _ _ | .advance j _ _ _ _ => actual i j

/-- Installed strategy, fixed before choosing the hidden history. Several jobs
    of the same physical role must use its one local prescription. -/
structure Policy where
  Role : Type
  View : Role → Type
  Command : Role → Type
  prescribe : (r : Role) → View r → Command r

structure Operations (policy : Policy) where
  Id : Type
  start : Id → Nat
  Cursor : Id → Nat → Type
  entry : (op : Id) → Cursor op (start op)
  Done : Id → Nat → Type
  Stop : Id → Nat → Type
  actor : Id → policy.Role
  view : (op : Id) → Nat → policy.View (actor op)
  observed : (op : Id) → Nat → policy.Command (actor op) → Form
  follows : (op : Id) → {i j : Nat} → Cursor op i → Cursor op j → Prop

def Operations.atCut {π : Policy} (ops : Operations π) (op : ops.Id) (i : Nat) : Form :=
  ops.observed op i (π.prescribe (ops.actor op) (ops.view op i))

structure World where
  Query : Type
  Token : Type
  clock : BudgetClock Nat
  forward : ∀ i j c, clock.within i j c → i ≤ j
  policy : Policy
  ops : Operations policy
  demand : Query → Option ops.Id
  bad : (q : Query) → Nat → Type
  cap : (q : Query) → Nat → Type
  seed : (q : Query) → (i : Nat) → cap q i → Type
  keeps : (q : Query) → (i : Nat) → cap q i → cap q (i+1) → Prop
  initial : ∀ q x, seed q 0 x
  predecessor : ∀ q i x, Authority.SourceOrParent (seed q) (keeps q) i x
  owner : ∀ {q i x}, seed q i x → Token
  repairId : ∀ {q i x}, seed q i x → Option ops.Id
  covered : Token → Nat → Query → Prop
  stableCover : ∀ t i q, (¬ ¬ covered t i q) → covered t i q
  affects : Token → Query → Prop
  seedFoot : ∀ {q i x} (s : seed q i x), affects (owner s) q

abbrev Charge (W : World) (q : W.Query) (i : Nat) :=
  {t : W.Token // W.covered t i q ∧ W.affects t q}
abbrev Answer (W : World) (q : W.Query) (i : Nat) := W.bad q i → Charge W q i
abbrev Earlier (W : World) (n : Nat) := ∀ j, j < n → (q : W.Query) → Answer W q j

/-- Analytic queries used to certify a fixed event. These may observe the
    paid poststate; the participant's choice already factors through ops.view. -/
structure Reads (W : World) (n endpoint : Nat) where
  count : Nat
  cut : Fin count → Nat
  query : Fin count → W.Query
  earlier : ∀ k, cut k < n
  byEndpoint : ∀ k, cut k ≤ endpoint

abbrev Inputs {W : World} {n e : Nat} (r : Reads W n e) :=
  ∀ k, Answer W (r.query k) (r.cut k)

def supply {W : World} {n e : Nat} (history : Earlier W n) (r : Reads W n e) : Inputs r :=
  fun k => history (r.cut k) (r.earlier k) (r.query k)

abbrev Position (W : World) (op : W.ops.Id) := Σ i, W.ops.Cursor op i

def opening (W : World) (op : W.ops.Id) : Position W op :=
  ⟨W.ops.start op,W.ops.entry op⟩

def jobClock (W : World) (op : W.ops.Id) : BudgetClock (Position W op) where
  within p q c := W.clock.within p.1 q.1 c
  now p := W.clock.now p.1
  append := W.clock.append

structure Job (W : World) (n : Nat) (op : W.ops.Id) where
  rank : Position W op → Nat
  remaining : Position W op → Nat
  reads : (p : Position W op) → Nat → Reads W n ((W.ops.atCut op p.1).endpoint p.1)
  step : ∀ p spent, W.clock.within (W.ops.start op) p.1 spent →
    spent + remaining p ≤ remaining (opening W op) → Inputs (reads p spent) →
    {v : Local (jobClock W op) (fun j => W.ops.Done op j.1) (fun j => W.ops.Stop op j.1)
        rank remaining p // form Sigma.fst v = W.ops.atCut op p.1 ∧
          cursorFollows (fun a b => W.ops.follows op a.2 b.2) v}

def Job.budget {W : World} {n : Nat} {op : W.ops.Id} (job : Job W n op) : Nat :=
  job.remaining (opening W op)

def Job.run {W : World} {n : Nat} {op : W.ops.Id}
    (job : Job W n op) (history : Earlier W n) :
    Arrival W.clock (Disposition (W.ops.Done op) (W.ops.Stop op))
      (W.ops.start op) job.budget := by
  let a := closeInBudget (jobClock W op) (fun j => W.ops.Done op j.1) (fun j => W.ops.Stop op j.1)
    job.rank job.remaining (opening W op) (fun p spent same fits =>
      (job.step p spent same fits (supply history (job.reads p spent))).val)
  refine ⟨a.point.1,a.elapsed,a.fits,a.sameRun,?_⟩
  cases a.result with
  | closed cert => exact .closed cert
  | charged receipt => exact .charged receipt

/-- The operation identity is attached to this birth/release in the source.
    A terminal and a valid local transfer clear this mark at that cut. -/
structure Repair (W : World) (q : W.Query) (n birth : Nat) (first : W.cap q birth)
    (s : W.seed q birth first) where
  op : W.ops.Id
  boundId : W.repairId s = some op
  mark : (k : Nat) → W.cap q k → Prop
  born : mark birth first
  carry : ∀ k x y, W.keeps q k x y → mark k x → mark (k+1) y
  job : Job W n op
  afterBirth : birth ≤ W.ops.start op
  deadline : ∀ j c, W.clock.within (W.ops.start op) j c →
    c ≤ job.budget → j < n
  terminal : ∀ j, W.ops.Done op j → ∀ x, ¬ mark j x
  transfer : ∀ j, W.ops.Stop op j → ∀ x, ¬ mark j x

def Repair.fence {W : World} {q : W.Query} {n birth : Nat} {first : W.cap q birth}
    {s : W.seed q birth first} (p : Repair W q n birth first s) (history : Earlier W n) :
    Authority.Retirement (W.keeps q) W.clock first n := by
  let arrival := p.job.run history
  have clear : ∀ x, ¬ p.mark arrival.point x := by
    cases arrival.result with
    | closed done => exact p.terminal _ done
    | charged stop => exact p.transfer _ stop
  exact ⟨p.mark,p.born,p.carry,W.ops.start p.op,p.afterBirth,p.job.budget,
    ⟨arrival.point,arrival.elapsed,arrival.fits,arrival.sameRun,⟨clear⟩⟩,
    fun j c same fits => Nat.le_of_lt (p.deadline j c same fits)⟩

/-- An earlier failure can explain today's miss only by transport of the
    very same incident's time-window membership and consumer footprint. -/
structure Referral (W : World) (q : W.Query) (n : Nat) where
  other : W.Query
  cut : Nat
  earlier : cut < n
  bad : W.bad other cut
  transport : ∀ t, W.covered t cut other → W.affects t other →
    W.covered t n q ∧ W.affects t q

def Referral.follow {W : World} {q : W.Query} {n : Nat}
    (r : Referral W q n) (history : Earlier W n) : Charge W q n := by
  let t := history r.cut r.earlier r.other r.bad
  exact ⟨t.val,r.transport t.val t.property.1 t.property.2⟩

structure Miss (W : World) (q : W.Query) (n : Nat) (op : W.ops.Id) where
  job : Job W n op
  byChallenge : ∀ j c, W.clock.within (W.ops.start op) j c →
    c ≤ job.budget → W.ops.Stop op j → j ≤ n
  missing : ∀ j c, W.clock.within (W.ops.start op) j c →
    c ≤ job.budget → W.ops.Done op j → False
  classify : ∀ j, j ≤ n → W.ops.Stop op j → W.cap q n ⊕ Referral W q n

structure Adapter (W : World) where
  active : ∀ q n, W.demand q = none → W.bad q n → W.cap q n
  missed : ∀ q n op, W.demand q = some op → W.bad q n → Miss W q n op
  repair : ∀ q n {r a} (s : W.seed q r a), r ≤ n → ¬ W.covered (W.owner s) n q →
    Repair W q n r a s

def attributeCap {W : World} (adapter : Adapter W) (n : Nat) (history : Earlier W n)
    (q : W.Query) (x : W.cap q n) : Charge W q n :=
  Authority.coveredOrigin W.clock W.forward (W.initial q) (W.predecessor q)
    W.owner (fun t k => W.covered t k q) (fun t k => W.stableCover t k q)
    (fun _ _ (_ : Unit) => True) (fun t _ => W.affects t q)
    (fun s _ _ => W.seedFoot s) (fun _ _ _ _ _ _ => True.intro) n x () True.intro
    (fun s before expired => (adapter.repair q n s before expired).fence history)

def resolveAt {W : World} (adapter : Adapter W) (n : Nat) (history : Earlier W n)
    (q : W.Query) (bad : W.bad q n) : Charge W q n := by
  cases h : W.demand q with
  | none => exact attributeCap adapter n history q (adapter.active q n h bad)
  | some op =>
    let miss := adapter.missed q n op h bad
    let a := miss.job.run history
    cases a.result with
    | closed result => exact False.elim (miss.missing _ _ a.sameRun a.fits result)
    | charged stop =>
      cases miss.classify _ (miss.byChallenge _ _ a.sameRun a.fits stop) stop with
      | inl residue => exact attributeCap adapter n history q residue
      | inr prior => exact prior.follow history

/-- Finite-prefix closure across roles. It constructs a covering token for
    each failure with the local source certificates. -/
def effectiveSupport {W : World} (adapter : Adapter W) (n : Nat) :
    (q : W.Query) → Answer W q n :=
  resolveAt adapter n (fun j _earlier => effectiveSupport adapter j)
termination_by n

def obtainAvailable {W : World} {q : W.Query} {n : Nat} {Good : Type}
    (answer : Answer W q n) (classify : Good ⊕ W.bad q n)
    (outside : ∀ t, W.covered t n q → ¬ W.affects t q) : Good := by
  cases classify with
  | inl good => exact good
  | inr bad =>
    let charge := answer bad
    exact False.elim (outside charge.val charge.property.1 charge.property.2)

/-- An adapter is needed on every member of the declared scenario/run family.
    Fixing the installed policy here prevents choosing one strategy per run.
    Coverage of all physical maximal runs is the source interpretation's duty. -/
structure Family where
  Run : Type
  policy : Policy
  world : Run → World
  samePolicy : ∀ r, (world r).policy = policy
  adapter : (r : Run) → Adapter (world r)

def Family.support (F : Family) (r : F.Run) (n : Nat) :
    (q : (F.world r).Query) → Answer (F.world r) q n :=
  effectiveSupport (F.adapter r) n

#print axioms Family.support
#print axioms effectiveSupport
#print axioms obtainAvailable
end RecurrentSupport
