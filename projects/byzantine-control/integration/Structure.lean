import Std

/-!
Constructive local-view gluing and its robust control interpretation.
The finite algorithm is in structure_model.py; no source-model fidelity claim
follows from Lean checking alone.
-/
namespace ByzantineStructure

abbrev Assignment (V A : Type) := V → A
abbrev Scope (V : Type) := V → Prop
abbrev Relation (V A : Type) := Assignment V A → Prop

def Agrees (S : Scope V) (a b : Assignment V A) : Prop :=
  ∀ v, S v → a v = b v

def Scoped (S : Scope V) (R : Relation V A) : Prop :=
  ∀ a b, Agrees S a b → R a → R b

noncomputable def merge (S : Scope V) (a b : Assignment V A) : Assignment V A :=
  fun v => if Classical.propDecidable (S v) |>.decide then b v else a v

-- A simpler proof interface for the same decidable conditional.
theorem merge_in (S : Scope V) (a b : Assignment V A) (v : V) (h : S v) :
    merge S a b v = b v := by
  simp [merge, h]

theorem merge_out (S : Scope V) (a b : Assignment V A) (v : V) (h : ¬ S v) :
    merge S a b v = a v := by
  simp [merge, h]

theorem merge_new (S : Scope V) (a b : Assignment V A) :
    Agrees S (merge S a b) b := by
  intro v hv
  exact merge_in S a b v hv

theorem merge_old (S T : Scope V) (a b : Assignment V A)
    (agree : Agrees (fun v => S v ∧ T v) a b) :
    Agrees T (merge S a b) a := by
  intro v hv
  by_cases hs : S v
  · rw [merge_in S a b v hs]
    exact (agree v ⟨hs, hv⟩).symm
  · exact merge_out S a b v hs

def Semijoin (S T : Scope V) (R U : Relation V A) : Relation V A :=
  fun a => R a ∧ ∃ b, U b ∧ Agrees (fun v => S v ∧ T v) a b

theorem semijoin_preserves_join (S T : Scope V) (R U : Relation V A)
    (a : Assignment V A) :
    (R a ∧ U a) ↔ (Semijoin S T R U a ∧ U a) := by
  constructor
  · rintro ⟨hr, hu⟩
    exact ⟨⟨hr, a, hu, fun _ _ => rfl⟩, hu⟩
  · rintro ⟨⟨hr, _⟩, hu⟩
    exact ⟨hr, hu⟩

/- An ordered rooted join tree is supplied by parent k < k. The running
intersection condition and parent-to-child row extension are separately checked.
This theorem constructs a single valuation by merging rows. -/
theorem running_intersection_glue
    (N : Nat) (S : Nat → Scope V) (R : Nat → Relation V A) (parent : Nat → Nat)
    (locality : ∀ k, Scoped (S k) (R k))
    (earlier : ∀ n, n < N → parent (n+1) ≤ n)
    (running : ∀ n k v, n < N → k ≤ n → S (n+1) v → S k v → S (parent (n+1)) v)
    (extend : ∀ n a, n < N → R (parent (n+1)) a →
      ∃ b, R (n+1) b ∧ Agrees (fun v => S (n+1) v ∧ S (parent (n+1)) v) a b)
    (root : ∃ a, R 0 a) :
    ∀ n, n ≤ N → ∃ a, ∀ k, k ≤ n → R k a := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨a, ha⟩ := root
    refine ⟨a, ?_⟩
    intro k hk
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact ha
  | succ n ih =>
    intro bound
    have below : n < N := by omega
    obtain ⟨a, ha⟩ := ih (by omega)
    obtain ⟨b, hb, hab⟩ := extend n a below (ha _ (earlier n below))
    refine ⟨merge (S (n+1)) a b, ?_⟩
    intro k hk
    by_cases heq : k = n+1
    · subst k
      exact locality (n+1) b _ (fun v hv => (merge_new (S (n+1)) a b v hv).symm) hb
    · have hkn : k ≤ n := by omega
      apply locality k a _ ?_ (ha k hkn)
      intro v hv
      have overlap : Agrees (fun v => S (n+1) v ∧ S k v) a b := by
        intro w hw
        exact hab w ⟨hw.1, running n k w below hkn hw.1 hw.2⟩
      exact (merge_old (S (n+1)) (S k) a b overlap v hv).symm


/- Removing genuinely unconsumed variables is an exact projection. Applying this
to absent invocations requires the source masks; arbitrary Kernels need not
ignore unissued values. The fallback is chosen before any scenario is known. -/
def restrictTo (live : Scope V) (a : Assignment V A) : {v : V // live v} → A :=
  fun v => a v.val

noncomputable def extendFrom (live : Scope V) (fallback : Assignment V A)
    (a : {v : V // live v} → A) : Assignment V A := by
  classical
  exact fun v => if h : live v then a ⟨v,h⟩ else fallback v

theorem restrict_extend (live : Scope V) (fallback : Assignment V A)
    (a : {v : V // live v} → A) :
    restrictTo live (extendFrom live fallback a) = a := by
  classical
  funext v
  simp [restrictTo, extendFrom, v.property]

def Cylinder (live : Scope V) (R : ({v : V // live v} → A) → Prop) : Relation V A :=
  fun a => R (restrictTo live a)

theorem cylinder_ignores_ghosts (live : Scope V)
    (R : ({v : V // live v} → A) → Prop) (a b : Assignment V A)
    (same : Agrees live a b) :
    Cylinder live R a ↔ Cylinder live R b := by
  have equal : restrictTo live a = restrictTo live b := by
    funext v
    exact same v.val v.property
  simp only [Cylinder, equal]

theorem cylinder_nonempty_iff (live : Scope V) (fallback : Assignment V A)
    (R : ({v : V // live v} → A) → Prop) :
    (∃ a, Cylinder live R a) ↔ ∃ b, R b := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨restrictTo live a, ha⟩
  · rintro ⟨b, hb⟩
    refine ⟨extendFrom live fallback b, ?_⟩
    simpa only [Cylinder, restrict_extend] using hb


/- Robust rows retain the SAME fault in evidence, compliance, physical effects,
and next-state obligations. X may include predecision reports, queues and memory. -/
structure Kernel (I F X O A : Type) where
  view : I → X → O
  compliant : F → I → Prop
  next : F → X → (I → A) → X → Prop
  edgeGood : F → X → (I → A) → X → Prop

def Follows (K : Kernel I F X O A) (f : F) (x : X)
    (p : Assignment (I × O) A) (actions : I → A) : Prop :=
  ∀ i, K.compliant f i → actions i = p (i, K.view i x)

def decisionScope (K : Kernel I F X O A) (f : F) (x : X) : Scope (I × O) :=
  fun v => K.compliant f v.1 ∧ K.view v.1 x = v.2

def robustRow (K : Kernel I F X O A) (Q : F → X → Prop) (f : F) (x : X) :
    Relation (I × O) A :=
  fun p =>
    (∀ actions, Follows K f x p actions → ∃ y, K.next f x actions y) ∧
    (∀ actions y, Follows K f x p actions → K.next f x actions y →
      K.edgeGood f x actions y ∧ Q f y)

theorem follows_transport (K : Kernel I F X O A) (f : F) (x : X)
    (p q : Assignment (I × O) A)
    (same : Agrees (decisionScope K f x) p q) (actions : I → A)
    (h : Follows K f x p actions) : Follows K f x q actions := by
  intro i hi
  exact (h i hi).trans (same (i, K.view i x) ⟨hi, rfl⟩)

theorem robust_row_scoped (K : Kernel I F X O A) (Q : F → X → Prop)
    (f : F) (x : X) : Scoped (decisionScope K f x) (robustRow K Q f x) := by
  intro p q same hp
  have back : Agrees (decisionScope K f x) q p := fun v hv => (same v hv).symm
  constructor
  · intro actions hq
    exact hp.1 actions (follows_transport K f x q p back actions hq)
  · intro actions y hq next
    exact hp.2 actions y (follows_transport K f x q p back actions hq) next

def Joint (K : Kernel I F X O A) (Q : F → X → Prop)
    (p : Assignment (I × O) A) : Prop :=
  ∀ f x, Q f x → robustRow K Q f x p

def LocalPolicy (I O A : Type) := I → O → A

def flatten (p : LocalPolicy I O A) : Assignment (I × O) A :=
  fun v => p v.1 v.2

def unflatten (p : Assignment (I × O) A) : LocalPolicy I O A :=
  fun i o => p (i, o)

theorem flatten_unflatten (p : Assignment (I × O) A) :
    flatten (unflatten p) = p := rfl

theorem unflatten_flatten (p : LocalPolicy I O A) :
    unflatten (flatten p) = p := rfl

theorem exact_local_policy_characterization (K : Kernel I F X O A) (Q : F → X → Prop) :
    (∃ a, Joint K Q a) ↔
    (∃ p : LocalPolicy I O A, ∀ f x, Q f x → robustRow K Q f x (flatten p)) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨unflatten a, ha⟩
  · rintro ⟨p, hp⟩
    exact ⟨flatten p, hp⟩


/- Per-scenario bag coverage connects the constructive join to actual control
rows. It supplies local soundness, not existence of a compatible policy. -/
theorem acyclic_kernel_synthesis (K : Kernel I F X O A) (Q : F → X → Prop)
    (N : Nat) (S : Nat → Scope (I × O)) (R : Nat → Relation (I × O) A)
    (parent : Nat → Nat)
    (locality : ∀ k, Scoped (S k) (R k))
    (earlier : ∀ n, n < N → parent (n+1) ≤ n)
    (running : ∀ n k v, n < N → k ≤ n → S (n+1) v → S k v → S (parent (n+1)) v)
    (extend : ∀ n a, n < N → R (parent (n+1)) a →
      ∃ b, R (n+1) b ∧ Agrees (fun v => S (n+1) v ∧ S (parent (n+1)) v) a b)
    (root : ∃ a, R 0 a)
    (coverage : ∀ f x, Q f x →
      ∃ k, k ≤ N ∧ ∀ a, R k a → robustRow K Q f x a) :
    ∃ p : LocalPolicy I O A, Joint K Q (flatten p) := by
  obtain ⟨a, ha⟩ := running_intersection_glue N S R parent locality earlier running extend root N (by omega)
  refine ⟨unflatten a, ?_⟩
  intro f x hx
  obtain ⟨k, bound, sound⟩ := coverage f x hx
  exact sound a (ha k bound)


theorem joined_rows_preserve_runs (K : Kernel I F X O A) (Q InitialGood : F → X → Prop)
    (p : Assignment (I × O) A) (joint : Joint K Q p)
    (f : F) (run : Nat → X) (actions : Nat → I → A)
    (initial : Q f (run 0)) (initial_good : InitialGood f (run 0))
    (follows : ∀ t, Follows K f (run t) p (actions t))
    (steps : ∀ t, K.next f (run t) (actions t) (run (t+1))) :
    InitialGood f (run 0) ∧ ∀ t, Q f (run t) ∧ K.edgeGood f (run t) (actions t) (run (t+1)) := by
  have invariant : ∀ t, Q f (run t) := by
    intro t
    induction t with
    | zero => exact initial
    | succ t ih => exact ((joint f (run t) ih).2 _ _ (follows t) (steps t)).2
  refine ⟨initial_good, ?_⟩
  intro t
  exact ⟨invariant t, ((joint f (run t) (invariant t)).2 _ _ (follows t) (steps t)).1⟩

theorem joined_rows_nonblocking (K : Kernel I F X O A) (Q : F → X → Prop)
    (p : Assignment (I × O) A) (joint : Joint K Q p)
    (f : F) (x : X) (hx : Q f x) :
    ∃ y, K.next f x (fun i => p (i, K.view i x)) y := by
  exact (joint f x hx).1 _ (fun _ _ => rfl)

/- Optional-resource order: the task, fault/effect relation and policy witnesses
stay fixed. An available resource set restricts which policies may be selected. -/
def ResourceFeasible (good : P → Prop) (uses : P → R → Prop) (available : R → Prop) : Prop :=
  ∃ p, good p ∧ ∀ r, uses p r → available r

theorem optional_resources_monotone (good : P → Prop) (uses : P → R → Prop)
    (small large : R → Prop) (included : ∀ r, small r → large r) :
    ResourceFeasible good uses small → ResourceFeasible good uses large := by
  rintro ⟨p, hp, enough⟩
  exact ⟨p, hp, fun r hr => included r (enough r hr)⟩

def ContainsSupport (supports : (R → Prop) → Prop) (available : R → Prop) : Prop :=
  ∃ support, supports support ∧ ∀ r, support r → available r

def HitsEvery (supports : (R → Prop) → Prop) (unavailable : R → Prop) : Prop :=
  ∀ support, supports support → ∃ r, support r ∧ unavailable r

theorem support_obstruction_dual (supports : (R → Prop) → Prop) (available : R → Prop) :
    ¬ ContainsSupport supports available ↔ HitsEvery supports (fun r => ¬ available r) := by
  classical
  constructor
  · intro noSupport support hs
    apply Classical.byContradiction
    intro noHit
    apply noSupport
    refine ⟨support, hs, ?_⟩
    intro r hr
    apply Classical.byContradiction
    intro absent
    exact noHit ⟨r, hr, absent⟩
  · intro hits ⟨support, hs, contained⟩
    obtain ⟨r, hr, absent⟩ := hits support hs
    exact absent (contained r hr)

end ByzantineStructure
