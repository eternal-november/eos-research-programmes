import Execution

/-! Dynamic compliance is analyst data, never a local observation.
This is a conservative command envelope for the addressed source interpreter.
Its static specialization is exact. It supplies no winning-policy premise. -/
namespace ByzantineJointEvolution
open ByzantineControlProgram

structure DynamicModel (I X : Type) (H A : I → Type) (F : Type) where
  observe : (i : I) → X → H i
  nominal : F → X → I → Prop
  initial : F → X → Prop
  next : F → X → ((i : I) → A i) → X → Prop

def DFollows (M : DynamicModel I X H A F) (f : F) (p : Policy I H A)
    (x : X) (a : (i : I) → A i) : Prop :=
  ∀ i, M.nominal f x i → a i = p i (M.observe i x)

def DStep (M : DynamicModel I X H A F) (f : F) (p : Policy I H A)
    (x y : X) : Prop := ∃ a, DFollows M f p x a ∧ M.next f x a y

def ofStatic (M : Model I X H A F) : DynamicModel I X H A F where
  observe := M.observe
  nominal := fun f _ i => M.correct f i
  initial := M.initial
  next := M.next

theorem static_step_exact (M : Model I X H A F) (f : F)
    (p : Policy I H A) (x y : X) :
    DStep (ofStatic M) f p x y ↔ Step M f p x y := Iff.rfl

theorem static_run_exact (M : Model I X H A F) (f : F)
    (p : Policy I H A) (run : Nat → X) :
    ((ofStatic M).initial f (run 0) ∧ ∀ t, DStep (ofStatic M) f p (run t) (run (t+1))) ↔
    (M.initial f (run 0) ∧ ∀ t, Step M f p (run t) (run (t+1))) := Iff.rfl

theorem dynamic_locality (M : DynamicModel I X H A F) (f g : F)
    (p : Policy I H A) (x y : X) (a b : (i : I) → A i) (i : I)
    (ha : DFollows M f p x a) (hb : DFollows M g p y b)
    (hx : M.nominal f x i) (hy : M.nominal g y i)
    (view : M.observe i x = M.observe i y) : a i = b i := by
  rw [ha i hx, hb i hy, view]

/- A source interpreter proves emitted commands satisfy DFollows at states in
which its actual code/configuration has the prescribed semantics. Other outputs
are retained in next, not erased. -/
theorem source_step_refines (M : DynamicModel I X H A F) (f : F)
    (p : Policy I H A) (x y : X) (emitted : (i : I) → A i)
    (interpret : ∀ i, M.nominal f x i → emitted i = p i (M.observe i x))
    (effects : M.next f x emitted y) : DStep M f p x y :=
  ⟨emitted, interpret, effects⟩

/- Dependency impairment is an effect overapproximation, not permission
for a source adversary to choose an output it cannot actually realize. -/
def EffectFits {I : Type} {A : I → Type} (physical nominal : (i : I) → A i → Prop)
    (impaired : I → Prop) (actual : (i : I) → A i) : Prop :=
  ∀ i, physical i (actual i) ∧ (¬ impaired i → nominal i (actual i))

theorem enlarge_impaired {I : Type} {A : I → Type}
    (physical nominal : (i : I) → A i → Prop) (J K : I → Prop)
    (actual : (i : I) → A i) (inclusion : ∀ i, J i → K i)
    (fit : EffectFits physical nominal J actual) : EffectFits physical nominal K actual := by
  intro i
  exact ⟨(fit i).1, fun hk => (fit i).2 (fun hj => hk (inclusion i hj))⟩

def DependencyProjection {Capability I : Type} (held : Capability → Prop)
    (footprint : Capability → I → Prop) (i : I) : Prop :=
  ∃ c, held c ∧ footprint c i

theorem dependency_projection_monotone {Capability I : Type}
    (held more : Capability → Prop) (footprint : Capability → I → Prop)
    (inclusion : ∀ c, held c → more c) (i : I)
    (hit : DependencyProjection held footprint i) : DependencyProjection more footprint i := by
  obtain ⟨c,hc,hi⟩ := hit
  exact ⟨c,inclusion c hc,hi⟩

structure StoreState where
  cells : Nat → Bool
  access : Bool
  learned : List Nat
  worldQueue : List Bool

def release (s : StoreState) : StoreState := { s with access := false }

theorem release_keeps_residuals (s : StoreState) :
    (release s).cells = s.cells ∧ (release s).learned = s.learned ∧
    (release s).worldQueue = s.worldQueue := ⟨rfl,rfl,rfl⟩

def changeCell (s : StoreState) (a : Nat) (v : Bool) : StoreState :=
  { s with cells := fun b => if b = a then v else s.cells b }

theorem write_keeps_knowledge_queue (s : StoreState) (a : Nat) (v : Bool) :
    (changeCell s a v).learned = s.learned ∧
    (changeCell s a v).worldQueue = s.worldQueue := ⟨rfl,rfl⟩

/- Addressed acquisition events count occurrence, including reacquisition.
No equality test on the target name can suppress the count. -/
structure AccessState where
  active : Nat → Bool
  eventCount : Nat
  learned : List Nat

def acquire (s : AccessState) (target key : Nat) : AccessState :=
  { active := fun i => if i = target then true else s.active i
    eventCount := s.eventCount + 1
    learned := key :: s.learned }

def endAccess (s : AccessState) (target : Nat) : AccessState :=
  { s with active := fun i => if i = target then false else s.active i }

theorem reacquisition_counts (s : AccessState) (target k1 k2 : Nat) :
    (acquire (endAccess (acquire s target k1) target) target k2).eventCount =
      s.eventCount + 2 := by simp [acquire,endAccess,Nat.add_assoc]

def triggered (s : AccessState) (trigger : Bool) (target key : Nat) : AccessState :=
  if trigger then acquire s target key else s

theorem propagation_is_acquisition (s : AccessState) (target key : Nat) :
    triggered s true target key = acquire s target key := rfl

theorem release_does_not_revoke (s : AccessState) (target : Nat) :
    (endAccess s target).learned = s.learned := rfl

/- Window bookkeeping with explicit last-taint witnesses. RestoreAge is the
conclusion to establish operationally in RESTORATION, not a source axiom. -/
def Window (active : Nat → Nat → Prop) (H t i : Nat) : Prop :=
  ∃ s, s ≤ t ∧ t ≤ s + H ∧ active s i

theorem window_from_recent_taint (active : Nat → Nat → Prop) (H t i s : Nat)
    (before : s ≤ t) (recent : t ≤ s + H) (hit : active s i) :
    Window active H t i := ⟨s,before,recent,hit⟩

theorem window_monotone_horizon (active : Nat → Nat → Prop) (H K t i : Nat)
    (hk : H ≤ K) (hw : Window active H t i) : Window active K t i := by
  obtain ⟨s,hs,ht,ha⟩ := hw
  exact ⟨s,hs,by omega,ha⟩

#print axioms static_step_exact
#print axioms static_run_exact
#print axioms dynamic_locality
#print axioms source_step_refines
#print axioms enlarge_impaired
#print axioms dependency_projection_monotone
#print axioms release_keeps_residuals
#print axioms write_keeps_knowledge_queue
#print axioms reacquisition_counts
#print axioms propagation_is_acquisition
#print axioms release_does_not_revoke
#print axioms window_from_recent_taint
#print axioms window_monotone_horizon
end ByzantineJointEvolution
