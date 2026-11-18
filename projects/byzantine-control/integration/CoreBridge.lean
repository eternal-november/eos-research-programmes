import Execution

/- A mechanism-independent decision-boundary normal form for component faults.
   The effect relation receives only actually issued compliant commands. It itself
   retains ALL permitted faulty commands and independent physical effects.
   World contains the actual event/mission/resource state needed by the instance. -/
namespace ByzantineControlIntegration
open ByzantineControlProgram

structure CausalKernel (I World F : Type) (Mem Obs Cmd : I → Type) where
  correct : F → I → Prop
  initial : F → World → ((i : I) → Mem i) → Prop
  observations : F → World → ((i : I) → Option (Obs i)) → Prop
  effects : F → World → ((i : I) → Option (Obs i)) →
    ((i : I) → Option (Cmd i)) → World → Prop

structure Boundary (I World : Type) (Mem Obs : I → Type) where
  world : World
  memory : (i : I) → Mem i
  seen : (i : I) → Option (Obs i)

structure LocalProgram (I : Type) (Mem Obs Cmd : I → Type) where
  output : (i : I) → Mem i → Obs i → Cmd i
  update : (i : I) → Mem i → Obs i → Mem i
  fallback : (i : I) → Cmd i

abbrev LocalView (Mem Obs : I → Type) := fun i => Mem i × Option (Obs i)
abbrev LocalChoice (Mem Cmd : I → Type) := fun i => Cmd i × Mem i

def programPolicy (p : LocalProgram I Mem Obs Cmd) :
    Policy I (LocalView Mem Obs) (LocalChoice Mem Cmd) :=
  fun i h => match h.2 with
    | none => (p.fallback i,h.1)
    | some o => (p.output i h.1 o,p.update i h.1 o)

noncomputable def issuedMask (K : CausalKernel I W F Mem Obs Cmd) (f : F)
    (s : Boundary I W Mem Obs) (a : (i : I) → Cmd i × Mem i) :
    (i : I) → Option (Cmd i) := by
  classical
  exact fun i => if K.correct f i then s.seen i |>.map (fun _ => (a i).1) else none

noncomputable def memoryMask (K : CausalKernel I W F Mem Obs Cmd) (f : F)
    (s : Boundary I W Mem Obs) (a : (i : I) → Cmd i × Mem i) :
    (i : I) → Mem i := by
  classical
  exact fun i => if K.correct f i then
    match s.seen i with | none => s.memory i | some _ => (a i).2
    else s.memory i

noncomputable def boundaryModel (K : CausalKernel I W F Mem Obs Cmd) :
    Model I (Boundary I W Mem Obs) (LocalView Mem Obs) (LocalChoice Mem Cmd) F := {
  observe := fun i s => (s.memory i,s.seen i)
  correct := K.correct
  initial := fun f s => K.initial f s.world s.memory ∧ K.observations f s.world s.seen
  next := fun f s a t =>
    K.effects f s.world s.seen (issuedMask K f s a) t.world ∧
    t.memory = memoryMask K f s a ∧ K.observations f t.world t.seen }

def evalProfile (p : LocalProgram I Mem Obs Cmd) (s : Boundary I W Mem Obs) :
    (i : I) → Cmd i × Mem i :=
  fun i => programPolicy p i (s.memory i,s.seen i)

noncomputable def SourceRound (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (s t : Boundary I W Mem Obs) : Prop :=
  K.effects f s.world s.seen (issuedMask K f s (evalProfile p s)) t.world ∧
    t.memory = memoryMask K f s (evalProfile p s) ∧ K.observations f t.world t.seen

theorem follows_masks (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (s : Boundary I W Mem Obs)
    (a : (i : I) → Cmd i × Mem i)
    (ha : Follows (boundaryModel K) f (programPolicy p) s a) :
    issuedMask K f s a = issuedMask K f s (evalProfile p s) ∧
    memoryMask K f s a = memoryMask K f s (evalProfile p s) := by
  classical
  constructor
  · funext i
    by_cases hc : K.correct f i
    · have eq : a i = evalProfile p s i := ha i hc
      simp only [issuedMask, if_pos hc, eq]
    · simp only [issuedMask, if_neg hc]
  · funext i
    by_cases hc : K.correct f i
    · have eq : a i = evalProfile p s i := ha i hc
      simp only [memoryMask, if_pos hc, eq]
    · simp only [memoryMask, if_neg hc]

theorem core_step_iff_source_round (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (s t : Boundary I W Mem Obs) :
    Step (boundaryModel K) f (programPolicy p) s t ↔ SourceRound K p f s t := by
  constructor
  · rintro ⟨a,ha,he,hm,ho⟩
    have masks := follows_masks K p f s a ha
    rw [masks.1] at he
    rw [masks.2] at hm
    exact ⟨he,hm,ho⟩
  · intro hs
    exact ⟨evalProfile p s, (fun _ _ => rfl), hs⟩

theorem absent_is_not_a_command (K : CausalKernel I W F Mem Obs Cmd) (f : F)
    (s : Boundary I W Mem Obs) (a : (i : I) → Cmd i × Mem i)
    (i : I) (absent : s.seen i = none) :
    issuedMask K f s a i = none ∧ memoryMask K f s a i = s.memory i := by
  classical
  by_cases hc : K.correct f i <;>
    simp [issuedMask,memoryMask,hc,absent]

theorem faulty_program_output_not_trusted (K : CausalKernel I W F Mem Obs Cmd) (f : F)
    (s : Boundary I W Mem Obs) (a : (i : I) → Cmd i × Mem i)
    (i : I) (bad : ¬ K.correct f i) :
    issuedMask K f s a i = none ∧ memoryMask K f s a i = s.memory i := by
  classical
  simp [issuedMask,memoryMask,bad]

theorem active_program_realization (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (s : Boundary I W Mem Obs)
    (i : I) (o : Obs i) (correct : K.correct f i) (active : s.seen i = some o) :
    issuedMask K f s (evalProfile p s) i = some (p.output i (s.memory i) o) ∧
    memoryMask K f s (evalProfile p s) i = p.update i (s.memory i) o := by
  classical
  simp [issuedMask,memoryMask,correct,active,evalProfile,programPolicy]

theorem core_run_iff_source_rounds (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (r : Nat → Boundary I W Mem Obs) :
    IsRun (boundaryModel K) (programPolicy p) f r ↔
      (K.initial f (r 0).world (r 0).memory ∧ K.observations f (r 0).world (r 0).seen) ∧
      ∀ t, SourceRound K p f (r t) (r (t+1)) := by
  constructor
  · rintro ⟨hi,hs⟩
    exact ⟨hi,fun t => (core_step_iff_source_round K p f _ _).mp (hs t)⟩
  · rintro ⟨hi,hs⟩
    exact ⟨hi,fun t => (core_step_iff_source_round K p f _ _).mpr (hs t)⟩

/- Totality is a primitive-interface obligation, not a safety assumption.
   Kernels with missing continuations must first use the documented losing sink. -/
theorem boundary_nonblocking (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd)
    (effects_total : ∀ f x o u, ∃ y, K.effects f x o u y)
    (observation_total : ∀ f x, ∃ o, K.observations f x o) :
    Nonblocking (boundaryModel K) (fun _ _ => True) (programPolicy p) := by
  intro f s _ a _
  obtain ⟨y,hy⟩ := effects_total f s.world s.seen (issuedMask K f s a)
  obtain ⟨o,ho⟩ := observation_total f y
  exact ⟨⟨y,memoryMask K f s a,o⟩,hy,rfl,ho⟩

/- Every old action-indexed model is a specialization. The existential profile
   retains its actual Byzantine choices; it is not a valid-action gate. -/
def legacyKernel (M : Model I X H A F) :
    CausalKernel I X F (fun _ => Unit) H A := {
  correct := M.correct
  initial := fun f x _ => M.initial f x
  observations := fun _ x o => o = fun i => some (M.observe i x)
  effects := fun f x _ issued y =>
    ∃ a, (∀ i, M.correct f i → issued i = some (a i)) ∧ M.next f x a y }

def legacyBoundary (M : Model I X H A F) (x : X) :
    Boundary I X (fun _ => Unit) H :=
  ⟨x,(fun _ => ()),fun i => some (M.observe i x)⟩

def legacyProgram (p : Policy I H A) (fallback : (i : I) → A i) :
    LocalProgram I (fun _ => Unit) H A :=
  ⟨fun i _ h => p i h, fun _ _ _ => (), fallback⟩

theorem legacy_initial (M : Model I X H A F) (f : F) (x : X) :
    (boundaryModel (legacyKernel M)).initial f (legacyBoundary M x) ↔ M.initial f x := by
  simp [boundaryModel,legacyKernel,legacyBoundary]

theorem legacy_step_iff (M : Model I X H A F) (p : Policy I H A)
    (fallback : (i : I) → A i) (f : F) (x y : X) :
    Step (boundaryModel (legacyKernel M)) f (programPolicy (legacyProgram p fallback))
      (legacyBoundary M x) (legacyBoundary M y) ↔ Step M f p x y := by
  rw [core_step_iff_source_round]
  constructor
  · rintro ⟨⟨a,ha,hn⟩,_,_⟩
    refine ⟨a,?_,hn⟩
    intro i hi
    have h := ha i hi
    simp [legacyKernel,issuedMask,legacyBoundary,evalProfile,programPolicy,legacyProgram,hi] at h
    exact h.symm
  · rintro ⟨a,ha,hn⟩
    refine ⟨⟨a,?_,hn⟩,?_,rfl⟩
    · intro i hi
      have h := ha i hi
      simp [legacyKernel,issuedMask,legacyBoundary,evalProfile,programPolicy,legacyProgram,hi,h]
    · funext i
      classical
      by_cases hi : M.correct f i <;>
        simp [legacyBoundary,memoryMask,legacyKernel,hi,evalProfile,programPolicy,legacyProgram]

theorem legacy_run_iff (M : Model I X H A F) (p : Policy I H A)
    (fallback : (i : I) → A i) (f : F) (r : Nat → X) :
    IsRun (boundaryModel (legacyKernel M)) (programPolicy (legacyProgram p fallback)) f
      (fun t => legacyBoundary M (r t)) ↔ IsRun M p f r := by
  constructor
  · rintro ⟨hi,hs⟩
    exact ⟨(legacy_initial M f _).mp hi,
      fun t => (legacy_step_iff M p fallback f _ _).mp (hs t)⟩
  · rintro ⟨hi,hs⟩
    exact ⟨(legacy_initial M f _).mpr hi,
      fun t => (legacy_step_iff M p fallback f _ _).mpr (hs t)⟩

#print axioms follows_masks
#print axioms core_step_iff_source_round
#print axioms absent_is_not_a_command
#print axioms faulty_program_output_not_trusted
#print axioms active_program_realization
#print axioms core_run_iff_source_rounds
#print axioms boundary_nonblocking
#print axioms legacy_initial
#print axioms legacy_step_iff
#print axioms legacy_run_iff

/- Reachable legacy-normal-form states contain no extra observational choices.
   This proves exhaustiveness of the embedding, not just preservation of images. -/
theorem legacy_boundary_canonical (M : Model I X H A F) (f : F)
    (s : Boundary I X (fun _ => Unit) H)
    (valid : (legacyKernel M).observations f s.world s.seen) :
    s = legacyBoundary M s.world := by
  cases s with
  | mk w mem seen =>
    have hm : mem = fun _ => () := funext (fun i => Subsingleton.elim _ _)
    have ho : seen = fun i => some (M.observe i w) := valid
    subst mem
    subst seen
    rfl

theorem legacy_run_exhaustive (M : Model I X H A F) (p : Policy I H A)
    (fallback : (i : I) → A i) (f : F)
    (r : Nat → Boundary I X (fun _ => Unit) H)
    (run : IsRun (boundaryModel (legacyKernel M))
      (programPolicy (legacyProgram p fallback)) f r) :
    (∀ t, r t = legacyBoundary M (r t).world) ∧
    IsRun M p f (fun t => (r t).world) := by
  have canonical : ∀ t, r t = legacyBoundary M (r t).world := by
    intro t
    cases t with
    | zero => exact legacy_boundary_canonical M f _ run.1.2
    | succ t =>
      obtain ⟨a,_,_,_,ho⟩ := run.2 t
      exact legacy_boundary_canonical M f _ ho
  refine ⟨canonical,?_⟩
  have init := run.1
  rw [canonical 0] at init
  refine ⟨(legacy_initial M f _).mp init,?_⟩
  intro t
  have edge := run.2 t
  rw [canonical t,canonical (t+1)] at edge
  exact (legacy_step_iff M p fallback f _ _).mp edge

theorem source_mission_transport (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd)
    (Good : F → (Nat → Boundary I W Mem Obs) → Prop)
    (won : ∀ f r,
      (K.initial f (r 0).world (r 0).memory ∧ K.observations f (r 0).world (r 0).seen) →
      (∀ t, SourceRound K p f (r t) (r (t+1))) → Good f r) :
    ∀ f r, IsRun (boundaryModel K) (programPolicy p) f r → Good f r := by
  intro f r hr
  have source := (core_run_iff_source_rounds K p f r).mp hr
  exact won f r source.1 source.2

#print axioms legacy_boundary_canonical
#print axioms legacy_run_exhaustive
#print axioms source_mission_transport

/- Initialization is a local controller parameter selected before f. It cannot
   secretly seed memory from the analyst's physical state or fault label. -/
def initializedBy {I W F : Type} {J Mem : I → Type} (Init : F → W → ((i : I) → J i) → Prop)
    (mu : (i : I) → J i → Mem i) (f : F) (x : W) (m : (i : I) → Mem i) : Prop :=
  ∃ inputs, Init f x inputs ∧ m = fun i => mu i (inputs i)

theorem local_initialization_covers {I W F : Type} {J Mem : I → Type} (Init : F → W → ((i : I) → J i) → Prop)
    (mu : (i : I) → J i → Mem i) (f : F) (x : W) (inputs : (i : I) → J i)
    (hi : Init f x inputs) :
    initializedBy Init mu f x (fun i => mu i (inputs i)) :=
  ⟨inputs,hi,rfl⟩

theorem same_initial_input_same_memory {I : Type} {J Mem : I → Type} (mu : (i : I) → J i → Mem i)
    (i : I) (inputs other : (i : I) → J i) (same : inputs i = other i) :
    mu i (inputs i) = mu i (other i) := by rw [same]

def updateOn (p : LocalProgram I Mem Obs Cmd) (i : I) (m : Mem i) :
    Option (Obs i) → Mem i
  | none => m
  | some o => p.update i m o

def callPrefix (seen : Nat → Option O) : Nat → List (Option O)
  | 0 => []
  | n+1 => callPrefix seen n ++ [seen n]

theorem fold_erases_missing_calls (p : LocalProgram I Mem Obs Cmd) (i : I)
    (signals : List (Option (Obs i))) (m : Mem i) :
    signals.foldl (updateOn p i) m =
      (signals.filterMap id).foldl (p.update i) m := by
  induction signals generalizing m with
  | nil => rfl
  | cons signal rest ih =>
    cases signal <;> simp [updateOn,List.foldl_cons,ih]

theorem source_memory_generated (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (r : Nat → Boundary I W Mem Obs)
    (steps : ∀ t, SourceRound K p f (r t) (r (t+1)))
    (i : I) (correct : K.correct f i) :
    ∀ t, (r t).memory i =
      (callPrefix (fun n => (r n).seen i) t).foldl (updateOn p i) ((r 0).memory i) := by
  classical
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := congrFun (steps t).2.1 i
    cases ho : (r t).seen i <;>
      simp [memoryMask,correct,ho,evalProfile,programPolicy] at hm
    · simpa [callPrefix,List.foldl_append,updateOn,ho,← ih] using hm
    · simpa [callPrefix,List.foldl_append,updateOn,ho,← ih] using hm

theorem source_memory_is_invocation_local (K : CausalKernel I W F Mem Obs Cmd)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (r : Nat → Boundary I W Mem Obs)
    (steps : ∀ t, SourceRound K p f (r t) (r (t+1)))
    (i : I) (correct : K.correct f i) (t : Nat) :
    (r t).memory i =
      ((callPrefix (fun n => (r n).seen i) t).filterMap id).foldl
        (p.update i) ((r 0).memory i) := by
  rw [source_memory_generated K p f r steps i correct t]
  exact fold_erases_missing_calls p i _ _

#print axioms local_initialization_covers
#print axioms same_initial_input_same_memory
#print axioms fold_erases_missing_calls
#print axioms source_memory_generated
#print axioms source_memory_is_invocation_local
theorem initialized_run_memory {J : I → Type}
    (K : CausalKernel I W F Mem Obs Cmd)
    (Init : F → W → ((i : I) → J i) → Prop) (mu : (i : I) → J i → Mem i)
    (localInit : ∀ f w m, K.initial f w m ↔ initializedBy Init mu f w m)
    (p : LocalProgram I Mem Obs Cmd) (f : F) (r : Nat → Boundary I W Mem Obs)
    (run : IsRun (boundaryModel K) (programPolicy p) f r) :
    ∃ inputs, Init f (r 0).world inputs ∧
      ∀ i, K.correct f i → ∀ t, (r t).memory i =
        ((callPrefix (fun n => (r n).seen i) t).filterMap id).foldl
          (p.update i) (mu i (inputs i)) := by
  have hs := (core_run_iff_source_rounds K p f r).mp run
  rcases (localInit f (r 0).world (r 0).memory).mp hs.1.1 with ⟨inputs, hi, hm⟩
  refine ⟨inputs, hi, ?_⟩
  intro i hc t
  rw [source_memory_is_invocation_local K p f r hs.2 i hc t, hm]

#print axioms initialized_run_memory
end ByzantineControlIntegration
