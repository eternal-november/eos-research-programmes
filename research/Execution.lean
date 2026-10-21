import Std

/-!
A distributed execution and whole-prefix prescription core.
X may contain global histories; H is the actual local observation/history type.
Fault identity is an external fixed index. Policies never receive that index.
This module proves its encoded discrete statements; THEORY.md supplies adapters.
-/
namespace ByzantineControlProgram

structure Model (I X : Type) (H A : I → Type) (F : Type) where
  observe : (i : I) → X → H i
  correct : F → I → Prop
  initial : F → X → Prop
  next : F → X → ((i : I) → A i) → X → Prop

abbrev Policy (I : Type) (H A : I → Type) := (i : I) → H i → A i
abbrev Family (F X : Type) := F → X → Prop

def Follows (M : Model I X H A F) (f : F) (p : Policy I H A)
    (x : X) (a : (i : I) → A i) : Prop :=
  ∀ i, M.correct f i → a i = p i (M.observe i x)

def Step (M : Model I X H A F) (f : F) (p : Policy I H A) (x y : X) : Prop :=
  ∃ a, Follows M f p x a ∧ M.next f x a y

def Post (M : Model I X H A F) (K : Family F X) (p : Policy I H A) : Family F X :=
  fun f y => ∃ x, K f x ∧ Step M f p x y

def Live (K : Family F X) : Prop := ∃ f x, K f x
def AllSafe (K S : Family F X) : Prop := ∀ f x, K f x → S f x

/- Every joint action with the required honest components has a successor.
Illegality/rejection must be represented by next, not by an empty winning run set. -/
def Nonblocking (M : Model I X H A F) (K : Family F X) (p : Policy I H A) : Prop :=
  ∀ f x, K f x → ∀ a, Follows M f p x a → ∃ y, M.next f x a y

theorem follows_same_local_view (M : Model I X H A F) (f : F) (p : Policy I H A)
    (x y : X) (a : (i : I) → A i)
    (same : ∀ i, M.correct f i → M.observe i x = M.observe i y)
    (hx : Follows M f p x a) : Follows M f p y a := by
  intro i hi
  rw [← same i hi]
  exact hx i hi

theorem post_live (M : Model I X H A F) (K : Family F X) (p : Policy I H A)
    (live : Live K) (nb : Nonblocking M K p) : Live (Post M K p) := by
  obtain ⟨f, x, hx⟩ := live
  let a : (i : I) → A i := fun i => p i (M.observe i x)
  have follows : Follows M f p x a := fun _ _ => rfl
  obtain ⟨y, hy⟩ := nb f x hx a follows
  exact ⟨f, y, x, hx, a, follows, hy⟩

def Winning (M : Model I X H A F) (S : Family F X) :
    Nat → Family F X → Prop
  | 0, K => Live K ∧ AllSafe K S
  | n+1, K => Live K ∧ AllSafe K S ∧
      ∃ p, Nonblocking M K p ∧ Winning M S n (Post M K p)

def SafePlan (M : Model I X H A F) (S : Family F X) :
    List (Policy I H A) → Family F X → Prop
  | [], K => Live K ∧ AllSafe K S
  | p :: ps, K => Live K ∧ AllSafe K S ∧
      Nonblocking M K p ∧ SafePlan M S ps (Post M K p)

/- Exact finite-horizon characterization. A single prescription handles all f,x in K.
The recursive update does not branch on an analyst's actual world. -/
theorem winning_iff_plan (M : Model I X H A F) (S : Family F X)
    (n : Nat) (K : Family F X) :
    Winning M S n K ↔ ∃ ps, ps.length = n ∧ SafePlan M S ps K := by
  induction n generalizing K with
  | zero =>
    constructor
    · intro h
      exact ⟨[], rfl, h⟩
    · rintro ⟨ps, hp, hs⟩
      cases ps with
      | nil => exact hs
      | cons p ps => simp at hp
  | succ n ih =>
    constructor
    · rintro ⟨live, safe, p, nb, rest⟩
      obtain ⟨ps, len, good⟩ := (ih (Post M K p)).mp rest
      exact ⟨p :: ps, by simp [len], live, safe, nb, good⟩
    · rintro ⟨ps, len, good⟩
      cases ps with
      | nil => simp at len
      | cons p ps =>
        obtain ⟨live, safe, nb, rest⟩ := good
        have tailLen : ps.length = n := by simpa using len
        exact ⟨live, safe, p, nb, (ih (Post M K p)).mpr ⟨ps, tailLen, rest⟩⟩

def Reach (M : Model I X H A F) (K : Family F X) (p : Nat → Policy I H A) :
    Nat → Family F X
  | 0 => K
  | t+1 => Post M (Reach M K p t) (p t)

theorem run_in_reach (M : Model I X H A F) (K : Family F X)
    (p : Nat → Policy I H A) (f : F) (run : Nat → X)
    (initial : K f (run 0))
    (steps : ∀ t, Step M f (p t) (run t) (run (t+1))) :
    ∀ t, Reach M K p t f (run t) := by
  intro t
  induction t with
  | zero => exact initial
  | succ t ih => exact ⟨run t, ih, steps t⟩

theorem prescription_safety (M : Model I X H A F) (K S : Family F X)
    (p : Nat → Policy I H A) (f : F) (run : Nat → X)
    (initial : K f (run 0))
    (steps : ∀ t, Step M f (p t) (run t) (run (t+1)))
    (safe : ∀ t, AllSafe (Reach M K p t) S) :
    ∀ t, S f (run t) :=
  fun t => safe t f (run t) (run_in_reach M K p f run initial steps t)

def compile (clock : (i : I) → H i → Nat) (p : Nat → Policy I H A) : Policy I H A :=
  fun i h => p (clock i h) i h

theorem compile_follows (M : Model I X H A F) (clock : (i : I) → H i → Nat)
    (p : Nat → Policy I H A) (f : F) (x : X) (a : (i : I) → A i) (t : Nat)
    (clock_ok : ∀ i, M.correct f i → clock i (M.observe i x) = t) :
    Follows M f (compile clock p) x a ↔ Follows M f (p t) x a := by
  constructor <;> intro h i hi
  · simpa [compile, clock_ok i hi] using h i hi
  · simpa [compile, clock_ok i hi] using h i hi

/- A nonblocking invariant produces an actual infinite run, using classical choice
only for the environment successors. The concrete controller remains the supplied p. -/
theorem infinite_run_exists (M : Model I X H A F) (S : Family F X)
    (p : Policy I H A) (f : F) (x0 : X) (initial : S f x0)
    (nb : Nonblocking M S p)
    (closed : ∀ x y, S f x → Step M f p x y → S f y) :
    ∃ run : Nat → X, run 0 = x0 ∧
      (∀ t, Step M f p (run t) (run (t+1))) ∧ ∀ t, S f (run t) := by
  classical
  let advance : {x : X // S f x} → {x : X // S f x} := fun x =>
    let a : (i : I) → A i := fun i => p i (M.observe i x.val)
    let follows : Follows M f p x.val a := fun _ _ => rfl
    let y := Classical.choose (nb f x.val x.property a follows)
    let hy := Classical.choose_spec (nb f x.val x.property a follows)
    ⟨y, closed x.val y x.property ⟨a, follows, hy⟩⟩
  let path : Nat → {x : X // S f x} := fun n => Nat.rec ⟨x0, initial⟩ (fun _ x => advance x) n
  refine ⟨fun n => (path n).val, rfl, ?_, fun t => (path t).property⟩
  intro t
  dsimp [path, advance]
  exact ⟨(fun i => p i (M.observe i (path t).val)), (fun _ _ => rfl),
    Classical.choose_spec (nb f (path t).val (path t).property
      (fun i => p i (M.observe i (path t).val)) (fun _ _ => rfl))⟩

def IsRun (M : Model I X H A F) (p : Policy I H A) (f : F) (run : Nat → X) : Prop :=
  M.initial f (run 0) ∧ ∀ t, Step M f p (run t) (run (t+1))

def liftPolicy (history : (i : I) → HC i → HA i) (act : (i : I) → HC i → AA i → AC i)
    (p : Policy I HA AA) : Policy I HC AC :=
  fun i h => act i h (p i (history i h))

/- The projection of Byzantine choices is analytic; the honest action lift above is local.
A concrete successor maps to an abstract successor at the SAME time index. -/
structure Refinement (C : Model I XC HC AC F) (A : Model I XA HA AA F)
    (history : (i : I) → HC i → HA i) (act : (i : I) → HC i → AA i → AC i)
    (p : Policy I HA AA) where
  state : XC → XA
  project : F → XC → ((i : I) → AC i) → ((i : I) → AA i)
  observes : ∀ i x, history i (C.observe i x) = A.observe i (state x)
  init : ∀ f x, C.initial f x → A.initial f (state x)
  follows : ∀ f x actions, Follows C f (liftPolicy history act p) x actions →
    Follows A f p (state x) (project f x actions)
  next : ∀ f x y actions, Follows C f (liftPolicy history act p) x actions →
    C.next f x actions y → A.next f (state x) (project f x actions) (state y)

theorem refinement_maps_run (C : Model I XC HC AC F) (A : Model I XA HA AA F)
    (history : (i : I) → HC i → HA i) (act : (i : I) → HC i → AA i → AC i) (p : Policy I HA AA)
    (R : Refinement C A history act p) (f : F) (run : Nat → XC)
    (valid : IsRun C (liftPolicy history act p) f run) :
    IsRun A p f (fun t => R.state (run t)) := by
  refine ⟨R.init f (run 0) valid.1, ?_⟩
  intro t
  obtain ⟨actions, follow, step⟩ := valid.2 t
  exact ⟨R.project f (run t) actions, R.follows f (run t) actions follow,
    R.next f (run t) (run (t+1)) actions follow step⟩

theorem refinement_transports_property (C : Model I XC HC AC F)
    (A : Model I XA HA AA F) (history : (i : I) → HC i → HA i)
    (act : (i : I) → HC i → AA i → AC i) (p : Policy I HA AA)
    (R : Refinement C A history act p)
    (abstractGood : F → (Nat → XA) → Prop) (concreteGood : F → (Nat → XC) → Prop)
    (won : ∀ f run, IsRun A p f run → abstractGood f run)
    (decode : ∀ f run, abstractGood f (fun t => R.state (run t)) → concreteGood f run) :
    ∀ f run, IsRun C (liftPolicy history act p) f run → concreteGood f run := by
  intro f run valid
  exact decode f run (won f (fun t => R.state (run t))
    (refinement_maps_run C A history act p R f run valid))

/- A finite monitor turns a bounded service-window requirement into safety.
Its tick is the declared execution time unit, not an inferred physical clock. -/
theorem bounded_service (served : Nat → Prop) (age : Nat → Nat) (bound : Nat)
    (update : ∀ t, ¬ served t → age (t+1) = age t + 1)
    (bounded : ∀ t, age t ≤ bound) :
    ∀ t, ∃ k, k ≤ bound ∧ served (t+k) := by
  intro t
  apply Classical.byContradiction
  intro no
  have absent : ∀ k, k ≤ bound → ¬ served (t+k) := by
    intro k hk hs
    exact no ⟨k, hk, hs⟩
  have grow : ∀ k, k ≤ bound+1 → age (t+k) = age t + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hkb : k ≤ bound := by omega
      have hki : k ≤ bound+1 := by omega
      have eq := update (t+k) (absent k hkb)
      have prev := ih hki
      have arith : t + (k+1) = (t+k)+1 := by omega
      rw [arith, eq, prev]
      omega
  have hg := grow (bound+1) (by omega)
  have hb := bounded (t+(bound+1))
  omega


theorem action_uniform_across_faults (M : Model I X H A F) (f g : F)
    (p : Policy I H A) (x y : X) (a b : (i : I) → A i) (i : I)
    (hf : M.correct f i) (hg : M.correct g i)
    (same : M.observe i x = M.observe i y)
    (ha : Follows M f p x a) (hb : Follows M g p y b) : a i = b i := by
  rw [ha i hf, hb i hg, same]

structure Clocked (M : Model I X H A F) where
  time : X → Nat
  localClock : (i : I) → H i → Nat
  readable : ∀ i x, localClock i (M.observe i x) = time x
  initial : ∀ f x, M.initial f x → time x = 0
  advances : ∀ f x a y, M.next f x a y → time y = time x + 1

theorem execution_time (M : Model I X H A F) (C : Clocked M)
    (p : Nat → Policy I H A) (f : F) (run : Nat → X)
    (init : M.initial f (run 0))
    (steps : ∀ t, Step M f (p t) (run t) (run (t+1))) :
    ∀ t, C.time (run t) = t := by
  intro t
  induction t with
  | zero => exact C.initial f (run 0) init
  | succ t ih =>
    obtain ⟨a, _, next⟩ := steps t
    rw [C.advances f (run t) a (run (t+1)) next, ih]

/- Exact compilation of the entire prescription sequence into one local-history policy.
A readable clock is a substantive hypothesis; unobservable stage changes do not qualify. -/
theorem compile_run_iff (M : Model I X H A F) (C : Clocked M)
    (p : Nat → Policy I H A) (f : F) (run : Nat → X) :
    (M.initial f (run 0) ∧ ∀ t, Step M f (p t) (run t) (run (t+1))) ↔
      IsRun M (compile C.localClock p) f run := by
  constructor
  · rintro ⟨init, steps⟩
    have time := execution_time M C p f run init steps
    refine ⟨init, ?_⟩
    intro t
    obtain ⟨a, follow, next⟩ := steps t
    refine ⟨a, ?_, next⟩
    exact (compile_follows M C.localClock p f (run t) a t
      (fun i _ => (C.readable i (run t)).trans (time t))).mpr follow
  · rintro ⟨init, steps⟩
    have time := execution_time M C (fun _ => compile C.localClock p) f run init steps
    refine ⟨init, ?_⟩
    intro t
    obtain ⟨a, follow, next⟩ := steps t
    refine ⟨a, ?_, next⟩
    exact (compile_follows M C.localClock p f (run t) a t
      (fun i _ => (C.readable i (run t)).trans (time t))).mp follow



/- Composition keeps each concrete action lift local and preserves the same fault/time index. -/
def composeRefinement
    (C : Model I XC HC AC F) (A : Model I XA HA AA F) (B : Model I XB HB AB F)
    (hCA : (i : I) → HC i → HA i) (aCA : (i : I) → HC i → AA i → AC i)
    (hAB : (i : I) → HA i → HB i) (aAB : (i : I) → HA i → AB i → AA i)
    (p : Policy I HB AB)
    (R : Refinement C A hCA aCA (liftPolicy hAB aAB p))
    (S : Refinement A B hAB aAB p) :
    Refinement C B (fun i h => hAB i (hCA i h))
      (fun i h b => aCA i h (aAB i (hCA i h) b)) p where
  state := fun x => S.state (R.state x)
  project := fun f x actions => S.project f (R.state x) (R.project f x actions)
  observes := by
    intro i x
    rw [R.observes i x, S.observes i (R.state x)]
  init := fun f x hx => S.init f (R.state x) (R.init f x hx)
  follows := by
    intro f x actions follow
    apply S.follows f (R.state x) (R.project f x actions)
    apply R.follows f x actions
    exact follow
  next := fun f x y actions follow h =>
    S.next f (R.state x) (R.state y) (R.project f x actions)
      (R.follows f x actions follow) (R.next f x y actions follow h)



/- Finite-branching compactness. This is a nonconstructive path-existence theorem,
not a finite-memory synthesis algorithm. -/
def Extends (children : X → List X) : Nat → X → Prop
  | 0, _ => True
  | n+1, x => ∃ y, y ∈ children x ∧ Extends children n y

theorem extends_mono (children : X → List X) (n m : Nat) (x : X)
    (le : m ≤ n) (h : Extends children n x) : Extends children m x := by
  induction n generalizing m x with
  | zero =>
    have : m = 0 := by omega
    subst m
    trivial
  | succ n ih =>
    cases m with
    | zero => trivial
    | succ m =>
      obtain ⟨y, hy, rest⟩ := h
      exact ⟨y, hy, ih m y (by omega) rest⟩

theorem finite_persistent_choice (xs : List X) (P : Nat → X → Prop)
    (down : ∀ n m x, m ≤ n → P n x → P m x)
    (all : ∀ n, ∃ x, x ∈ xs ∧ P n x) :
    ∃ x, x ∈ xs ∧ ∀ n, P n x := by
  classical
  induction xs with
  | nil =>
    obtain ⟨x, bad, _⟩ := all 0
    simp at bad
  | cons a xs ih =>
    by_cases yes : ∀ n, P n a
    · exact ⟨a, by simp, yes⟩
    · have some : ∃ n, ¬ P n a := Classical.not_forall.mp yes
      obtain ⟨k, hk⟩ := some
      have rest : ∀ n, ∃ x, x ∈ xs ∧ P n x := by
        intro n
        obtain ⟨x, hx, hp⟩ := all (max n k)
        have neq : x ≠ a := by
          intro eq
          subst x
          exact hk (down (max n k) k a (by omega) hp)
        have mem : x ∈ xs := by simpa [neq] using hx
        exact ⟨x, mem, down (max n k) n x (by omega) hp⟩
      obtain ⟨x, hx, hp⟩ := ih rest
      exact ⟨x, by simp [hx], hp⟩

theorem infinite_path_of_finite_extensions (children : X → List X) (root : X)
    (deep : ∀ n, Extends children n root) :
    ∃ path : Nat → X, path 0 = root ∧ ∀ t, path (t+1) ∈ children (path t) := by
  classical
  let Deep : X → Prop := fun x => ∀ n, Extends children n x
  have child : ∀ x, Deep x → ∃ y, y ∈ children x ∧ Deep y := by
    intro x hx
    exact finite_persistent_choice (children x) (fun n y => Extends children n y)
      (fun n m y hnm hy => extends_mono children n m y hnm hy)
      (fun n => hx (n+1))
  let advance : {x : X // Deep x} → {x : X // Deep x} := fun x =>
    ⟨Classical.choose (child x.val x.property),
     (Classical.choose_spec (child x.val x.property)).2⟩
  let path : Nat → {x : X // Deep x} :=
    fun n => Nat.rec ⟨root, deep⟩ (fun _ x => advance x) n
  refine ⟨fun n => (path n).val, rfl, ?_⟩
  intro t
  exact (Classical.choose_spec (child (path t).val (path t).property)).1



/- A finite trace table can be factored into a genuine local policy when issued actions
are uniform across every admissible pair of correct local-view occurrences. -/
theorem local_policy_factorization (M : Model I X H A F) (D : Family F X)
    (issued : (i : I) → F → X → A i) (fallback : (i : I) → A i)
    (uniform : ∀ i f g x y, D f x → D g y → M.correct f i → M.correct g i →
      M.observe i x = M.observe i y → issued i f x = issued i g y) :
    ∃ p : Policy I H A, ∀ i f x, D f x → M.correct f i →
      p i (M.observe i x) = issued i f x := by
  classical
  let W : (i : I) → H i → (F × X) → Prop :=
    fun i h w => D w.1 w.2 ∧ M.correct w.1 i ∧ M.observe i w.2 = h
  let p : Policy I H A := fun i h =>
    if hw : ∃ w, W i h w then
      issued i (Classical.choose hw).1 (Classical.choose hw).2
    else fallback i
  refine ⟨p, ?_⟩
  intro i f x hd hc
  have witnessExists : ∃ w, W i (M.observe i x) w := ⟨(f,x), hd, hc, rfl⟩
  have facts := Classical.choose_spec witnessExists
  dsimp [p]
  rw [dif_pos witnessExists]
  exact uniform i (Classical.choose witnessExists).1 f (Classical.choose witnessExists).2 x
    facts.1 hd facts.2.1 hc facts.2.2


#print axioms local_policy_factorization
#print axioms extends_mono
#print axioms finite_persistent_choice
#print axioms infinite_path_of_finite_extensions
#print axioms composeRefinement
#print axioms action_uniform_across_faults
#print axioms execution_time
#print axioms compile_run_iff
#print axioms follows_same_local_view
#print axioms post_live
#print axioms winning_iff_plan
#print axioms run_in_reach
#print axioms prescription_safety
#print axioms compile_follows
#print axioms infinite_run_exists
#print axioms refinement_maps_run
#print axioms refinement_transports_property
#print axioms bounded_service

end ByzantineControlProgram
