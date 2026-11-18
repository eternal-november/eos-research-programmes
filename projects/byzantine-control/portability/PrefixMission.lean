import RecurrentSupport

/-! Conjoining recurrent physical obligations on an initialized prefix.
The finite proof reads source-observed transfers and the identities of raw
incidents. The control policy reads only its actual local state and views. -/
namespace PrefixMission
open RecurrentSupport ContextualJobs

/-- Indexed to the actual stopped operation and its observed kind. A recorded
    origin may be an earlier captured reading or an actually opened obligation
    whose omission mattered at that stop. A verifier cannot choose a different
    provider trace after seeing which region is affordable. -/
structure Journal (W : World) where
  inputs : (op : W.ops.Id) → (j : Nat) → W.ops.Stop op j → List (Nat × W.Query)

/-- Source rules valid on a prefix, including the *entire* operation ball
    used to explain a missed deadline. No later observed Done may be used. -/
structure Patch {W : World} (journal : Journal W) (n : Nat) extends CutRule W n where
  missedByCut : ∀ q op (bound : W.demand q = some op) (bad : W.bad q n) j c,
    W.clock.within (W.ops.start op) j c →
    c ≤ (missed q op bound bad).job.budget → j ≤ n
  referred : ∀ q op (bound : W.demand q = some op) (bad : W.bad q n)
    j (hj : j ≤ n) (stop : W.ops.Stop op j) (earlier : Referral W q n),
    (missed q op bound bad).classify j hj stop = .inr earlier →
    (earlier.cut,earlier.other) ∈ journal.inputs op j stop ∧ earlier.cut ≤ j

def knownThrough {W : World} {journal : Journal W} {n : Nat} (patches : ∀ k, k ≤ n → Patch journal k) :
    ∀ q, Answer W q n :=
  through (fun k h => (patches k h).toCutRule) n (Nat.le_refl n)

structure Scale (D : Type) where
  zero : D
  add : D → D → D
  le : D → D → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
  mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)

def sum {D : Type} (s : Scale D) : List D → D
  | [] => s.zero
  | d :: ds => s.add d (sum s ds)

/-- A single raw common-window enumeration with consumer-relative tests.
    Conservative extra hits weaken the achievable arithmetic margin. -/
structure Window (W : World) (n : Nat) where
  tokens : List W.Token
  reaches : W.Token → W.Query → Bool
  contains : ∀ t q, W.covered t n q → W.affects t q → t ∈ tokens
  sound : ∀ t q, W.covered t n q → W.affects t q → reaches t q = true

def Window.mask {W : World} {n : Nat} (v : Window W n) (q : W.Query) : Bool :=
  v.tokens.any (fun t => v.reaches t q)

theorem Window.hit {W : World} {n : Nat} (v : Window W n) {q} (a : Charge W q n) :
    v.mask q = true :=
  List.any_eq_true.mpr ⟨a.val,v.contains _ _ a.property.1 a.property.2,
    v.sound _ _ a.property.1 a.property.2⟩

/-- One already weighted physical contribution to a named signed observable.
    Genuine receipts carry local pose, time, source, work and operating data
    as needed. Adverse exports need a hard bound at their true port. -/
structure Row (W : World) (n : Nat) {D : Type} (s : Scale D) where
  query : W.Query
  Good : Type
  classify : Good ⊕ W.bad query n
  actual : D
  nominal : D
  hard : D
  hardFloor : s.le hard actual
  normalFloor : Good → s.le nominal actual

def Row.floor {W : World} {n D} {s : Scale D} (row : Row W n s) (v : Window W n) : D :=
  if v.mask row.query then row.hard else row.nominal

theorem Row.bounded {W : World} {n D} {s : Scale D} (row : Row W n s) (v : Window W n)
    (answers : ∀ q, Answer W q n) : s.le (row.floor v) row.actual := by
  unfold Row.floor
  split
  · exact row.hardFloor
  · rename_i clear
    cases row.classify with
    | inl good => exact row.normalFloor good
    | inr bad => exact False.elim (clear (v.hit (answers row.query bad)))

theorem totalBound {W : World} {n D} {s : Scale D} (v : Window W n)
    (answers : ∀ q, Answer W q n) (rows : List (Row W n s)) :
    s.le (sum s (rows.map (fun r => r.floor v))) (sum s (rows.map Row.actual)) := by
  induction rows with
  | nil => exact s.refl _
  | cons head rest ih => exact s.mono (head.bounded v answers) ih

/-- The arithmetic check uses only the physical elementary floors and raw
    union, so it can precede any inference of healthy actual outputs. -/
theorem service {W : World} {D} {s : Scale D} {n : Nat}
    {journal : Journal W} (rules : ∀ k, k ≤ n → Patch journal k) (v : Window W n) (rows : List (Row W n s))
    (goal : D) (fits : s.le goal (sum s (rows.map (fun r => r.floor v)))) :
    s.le goal (sum s (rows.map Row.actual)) :=
  s.trans fits (totalBound v (knownThrough rules) rows)

/-- Each ballot is an installed logical slot in one actual observation
    window. The caller determines the deduplicated slots before this fold. -/
structure Ballot (W : World) (n : Nat) where
  query : W.Query
  yes : Bool
  Good : Type
  classify : Good ⊕ W.bad query n

def tally {α : Type u} (test : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if test x then 1 else 0) + tally test xs

structure Selected {W : World} {n : Nat} (v : Window W n) (xs : List (Ballot W n)) where
  ballot : Ballot W n
  occurs : ballot ∈ xs
  affirmed : ballot.yes = true
  outside : v.mask ballot.query = false
  receipt : ballot.Good

def findBallot {W : World} {n : Nat} (v : Window W n)
    (answers : ∀ q, Answer W q n) (xs : List (Ballot W n)) :
    Sum (Selected v xs) (PLift (tally Ballot.yes xs ≤ tally (fun b => v.mask b.query) xs)) :=
  match xs with
  | [] => .inr ⟨Nat.le_refl _⟩
  | a :: rest =>
    if ha : a.yes = true ∧ v.mask a.query = false then
      .inl ⟨a,List.Mem.head _,ha.1,ha.2,
        obtainAvailable (answers a.query) a.classify (fun t cov reaches => by
          have h := v.hit (q := a.query) ⟨t,cov,reaches⟩
          simp [ha.2] at h)⟩
    else
      match findBallot v answers rest with
      | .inl good => .inl ⟨good.ballot,List.Mem.tail _ good.occurs,good.affirmed,good.outside,good.receipt⟩
      | .inr few => .inr ⟨by
          have h := few.down
          cases hy : a.yes <;> cases hm : v.mask a.query <;>
            simp [tally, hy, hm] at * <;> omega⟩

/-- Extract an actual agreeing observation receipt, even when a few positive
    readings really do occur in the same common-cause footprint. -/
def guarded {W : World} {n : Nat} {journal : Journal W} (rules : ∀ k, k ≤ n → Patch journal k)
    (v : Window W n) (xs : List (Ballot W n))
    (more : tally (fun b => v.mask b.query) xs < tally Ballot.yes xs) : Selected v xs :=
  match findBallot v (knownThrough rules) xs with
  | .inl chosen => chosen
  | .inr few => False.elim (by have h := few.down; omega)

/-- One scalar component of the factual rule on the actual requested body
    and effect interval. Selection and effect verification are analytic;
    the actor sees only its ordinary inputs and threshold. -/
structure Factual {W : World} {n : Nat} (xs : List (Ballot W n)) {D : Type} (s : Scale D) where
  Instant : Type
  during : Instant → Prop
  actual : Instant → D
  reading : Ballot W n → D
  allowance : Ballot W n → D
  threshold : D
  limit : D
  observed : ∀ b, b ∈ xs → b.yes = true → b.Good → s.le (reading b) threshold
  evolves : ∀ b, b ∈ xs → b.Good → ∀ t, during t → s.le (actual t) (s.add (reading b) (allowance b))
  margin : ∀ b, b ∈ xs → s.le (s.add threshold (allowance b)) limit

theorem factual {W : World} {n D} {s : Scale D} {journal : Journal W}
    (rules : ∀ k, k ≤ n → Patch journal k) (v : Window W n) (xs : List (Ballot W n))
    (more : tally (fun b => v.mask b.query) xs < tally Ballot.yes xs) (law : Factual xs s) :
    ∀ t, law.during t → s.le (law.actual t) law.limit := by
  let g := guarded rules v xs more
  intro t ht
  exact s.trans (law.evolves g.ballot g.occurs g.receipt t ht)
    (s.trans (s.mono (law.observed g.ballot g.occurs g.affirmed g.receipt) (s.refl _))
      (law.margin g.ballot g.occurs))

/-- The missing release property cannot be recovered merely by observing no
    lingering bad output. Run the actual registered operation even if no later
    consumer emitted an error. Its terminal supplies both usability and the
    realized retirement, with a source-specific interrupt alternative. -/
def restored {W : World} {n : Nat} (rules : ∀ k, k < n → CutRule W k)
    {op : W.ops.Id} (job : Job W n op) (Useful Retired Interrupt : Nat → Type)
    (terminal : ∀ j, W.ops.Done op j → Useful j × Retired j)
    (stopped : ∀ j, W.ops.Stop op j → Interrupt j) :
    Arrival W.clock (fun j => (Useful j × Retired j) ⊕ Interrupt j)
      (W.ops.start op) job.budget := by
  let past : Earlier W n := fun j h => through (endCut := j)
    (fun k earlier => rules k (by omega)) j (Nat.le_refl j)
  let a := job.run past
  refine ⟨a.point,a.elapsed,a.fits,a.sameRun,?_⟩
  cases a.result with
  | closed done => exact .inl (terminal _ done)
  | charged stop => exact .inr (stopped _ stop)

/-- A source quietness fact excludes actual named interruptions. It has no
    authority to turn an unpaid or unfinished physical operation into a result. -/
def uninterrupted {W : World} {n : Nat} (rules : ∀ k, k < n → CutRule W k)
    {op : W.ops.Id} (job : Job W n op) (Useful Retired Interrupt : Nat → Type)
    (terminal : ∀ j, W.ops.Done op j → Useful j × Retired j)
    (stopped : ∀ j, W.ops.Stop op j → Interrupt j)
    (quiet : ∀ j c, W.clock.within (W.ops.start op) j c → c ≤ job.budget → Interrupt j → False) :
    Arrival W.clock (fun j => Useful j × Retired j) (W.ops.start op) job.budget := by
  let a := restored rules job Useful Retired Interrupt terminal stopped
  refine ⟨a.point,a.elapsed,a.fits,a.sameRun,?_⟩
  cases a.result with
  | inl good => exact good
  | inr hit => exact False.elim (quiet _ _ a.sameRun a.fits hit)

/-- The source's register of physical release occurrences is fixed before
    search for a successful continuation. Its interpretation is shared by all
    monitors of this run. The external decode covers *every* relevant release. -/
structure Releases (W : World) where
  Event : Type
  atRelease : Event → Nat
  invocation : Event → W.ops.Id
  query : Event → W.Query
  Useful : Event → Nat → Type
  Retired : Event → Nat → Type
  inherited : Event → Nat → W.Token → Type

structure Successor {W : World} (rs : Releases W) (e : rs.Event) (j : Nat) where
  charge : Charge W (rs.query e) j
  lineage : rs.inherited e j charge.val

/-- Launch and recovery time consume the *same* H from the real release.
    The launch path requires the actual independently due trigger or bounded
    sponsored scheduling, not a post hoc observation that a job finished. -/
structure Timely {W : World} (rs : Releases W) (e : rs.Event) (n H : Nat) where
  launch : Nat
  started : W.clock.within (rs.atRelease e) (W.ops.start (rs.invocation e)) launch
  job : Job W n (rs.invocation e)
  strict : launch + job.budget < H
  byCut : ∀ j c, W.clock.within (rs.atRelease e) j c → c ≤ launch + job.budget → j ≤ n
  good : ∀ j, W.ops.Done (rs.invocation e) j → rs.Useful e j × rs.Retired e j
  interrupted : ∀ j, W.ops.Stop (rs.invocation e) j → Successor rs e j

structure ReleaseResult {W : World} (rs : Releases W) (e : rs.Event) (n H : Nat) where
  point : Nat
  cost : Nat
  strict : cost < H
  byCut : point ≤ n
  fromRelease : W.clock.within (rs.atRelease e) point cost
  result : (rs.Useful e point × rs.Retired e point) ⊕ Successor rs e point

def releaseResult {W : World} (rs : Releases W) (e : rs.Event) {n H : Nat}
    {journal : Journal W} (rules : ∀ k, k < n → Patch journal k) (due : Timely rs e n H) : ReleaseResult rs e n H := by
  let old := restored (fun k h => (rules k h).toCutRule) due.job _ _ _ due.good due.interrupted
  have t : W.clock.within (rs.atRelease e) old.point (due.launch+old.elapsed) :=
    W.clock.append due.started old.sameRun
  have fit : due.launch+old.elapsed ≤ due.launch+due.job.budget := Nat.add_le_add_left old.fits _
  exact ⟨old.point,_,Nat.lt_of_le_of_lt fit due.strict,due.byCut _ _ t fit,t,old.result⟩

/-- An eligible release has a real useful/retired terminal unless a named
    incident inherited the particular outstanding physical liability. -/
def quietRelease {W : World} (rs : Releases W) (e : rs.Event) {n H : Nat}
    {journal : Journal W} (rules : ∀ k, k < n → Patch journal k) (due : Timely rs e n H)
    (quiet : ∀ j c, W.clock.within (rs.atRelease e) j c → c < H → Successor rs e j → False) :
    (j : Nat) × (c : Nat) × (PLift (c < H ∧ j ≤ n ∧ W.clock.within (rs.atRelease e) j c)
      × rs.Useful e j × rs.Retired e j) := by
  let result := releaseResult rs e rules due
  refine ⟨result.point,result.cost,⟨result.strict,result.byCut,result.fromRelease⟩,?_⟩
  cases result.result with
  | inl yes => exact yes
  | inr hit => exact False.elim (quiet _ _ result.fromRelease result.strict hit)

#print axioms releaseResult
#print axioms quietRelease
#print axioms RecurrentSupport.through
#print axioms Window.hit
#print axioms service
#print axioms guarded
#print axioms factual
#print axioms restored
#print axioms uninterrupted

end PrefixMission
