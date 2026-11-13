import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic

/-!
# Resource-sensitive observation-based construction

A generic interpreter for finite observation policies uses actual residual states.
The example separates worldwise constructibility plus exact diagnosis from one
uniform successful policy. A nondestructive measurement repairs the separation.

The primitive transition tables are supplied native semantics, not empirical
certificates for physical hardware. See `ResourceSensitiveLoop_SCOPE.md`.
-/

namespace ResourceSensitiveLoop

universe u v w z

/-- A deterministic, possibly disabled native action with an observable output. -/
structure Plant (World : Type u) (State : Type v) (Action : Type w) (Obs : Type z) where
  step : World → State → Action → Option (Obs × State)

/-- A well-founded observation tree. An action cannot inspect the hidden world.
When `Obs` is finite this is a finite tree, with no bound fixed in advance. -/
inductive Policy (Action : Type w) (Obs : Type z) : Type (max w z)
  | halt
  | act (action : Action) (next : Obs → Policy Action Obs)

namespace Policy

variable {World : Type u} {State : Type v} {Action : Type w} {Obs : Type z}

/-- Execute on the current physical state; `none` records a disabled action. -/
def run (plant : Plant World State Action Obs) (world : World) :
    Policy Action Obs → State → Option State
  | .halt, state => some state
  | .act action next, state =>
      match plant.step world state action with
      | none => none
      | some (obs, residual) => run plant world (next obs) residual

/-- Sequential composition does not reinitialize the physical state. -/
def append : Policy Action Obs → Policy Action Obs → Policy Action Obs
  | .halt, continuation => continuation
  | .act action next, continuation =>
      .act action (fun obs => append (next obs) continuation)

theorem run_append (plant : Plant World State Action Obs) (world : World)
    (first continuation : Policy Action Obs) (state : State) :
    run plant world (append first continuation) state =
      (run plant world first state).bind (run plant world continuation) := by
  induction first generalizing state with
  | halt => rfl
  | act action next ih =>
      simp only [append, run]
      cases h : plant.step world state action with
      | none => rfl
      | some output =>
          rcases output with ⟨obs, residual⟩
          simpa using ih obs residual

/-- Every finite successful execution preserves a transition invariant. -/
theorem run_preserves (plant : Plant World State Action Obs)
    (invariant : World → State → Prop)
    (preserved : ∀ world state action obs residual,
      invariant world state →
      plant.step world state action = some (obs, residual) →
      invariant world residual)
    (policy : Policy Action Obs) (world : World) (state residual : State)
    (initial : invariant world state)
    (execution : run plant world policy state = some residual) :
    invariant world residual := by
  induction policy generalizing state with
  | halt =>
      simp only [run, Option.some.injEq] at execution
      simpa [← execution] using initial
  | act action next ih =>
      cases hs : plant.step world state action with
      | none => simp [run, hs] at execution
      | some output =>
          rcases output with ⟨obs, state'⟩
          have h' : run plant world (next obs) state' = some residual := by
            simpa [run, hs] using execution
          exact ih obs state' (preserved world state action obs state' initial hs) h'

end Policy

section Generic

variable {World : Type u} {State : Type v} {Action : Type w} {Obs : Type z}

/-- Success includes executable termination at a goal, not just a conditional
preservation assertion that could hold vacuously for a disabled program. -/
def Successful (plant : Plant World State Action Obs) (goal : World → State → Prop)
    (world : World) (state : State) (policy : Policy Action Obs) : Prop :=
  ∃ residual, policy.run plant world state = some residual ∧ goal world residual

/-- Beliefs retain both world labels and actual physical residual states. -/
def update (plant : Plant World State Action Obs) (belief : Set (World × State))
    (action : Action) (obs : Obs) : Set (World × State) :=
  {output | ∃ prior, (output.1, prior) ∈ belief ∧
    plant.step output.1 prior action = some (obs, output.2)}

def Enabled (plant : Plant World State Action Obs) (belief : Set (World × State))
    (action : Action) : Prop :=
  ∀ world state, (world, state) ∈ belief →
    ∃ obs residual, plant.step world state action = some (obs, residual)

def UniformSuccess (plant : Plant World State Action Obs)
    (goal : World → State → Prop) (belief : Set (World × State))
    (policy : Policy Action Obs) : Prop :=
  ∀ world state, (world, state) ∈ belief → Successful plant goal world state policy

/-- Exact one-step obligation: one common enabled action, then one continuation
for each observation, valid on the actual residual belief. -/
theorem successful_act_iff (plant : Plant World State Action Obs)
    (goal : World → State → Prop) (world : World) (state : State)
    (action : Action) (next : Obs → Policy Action Obs) :
    Successful plant goal world state (.act action next) ↔
      ∃ obs residual, plant.step world state action = some (obs, residual) ∧
        Successful plant goal world residual (next obs) := by
  cases hs : plant.step world state action with
  | none => simp [Successful, Policy.run, hs]
  | some output =>
      rcases output with ⟨obs, residual⟩
      simp [Successful, Policy.run, hs]

theorem uniform_act_iff (plant : Plant World State Action Obs)
    (goal : World → State → Prop) (belief : Set (World × State))
    (action : Action) (next : Obs → Policy Action Obs) :
    UniformSuccess plant goal belief (.act action next) ↔
      Enabled plant belief action ∧
        ∀ obs, UniformSuccess plant goal (update plant belief action obs) (next obs) := by
  constructor
  · intro h
    constructor
    · intro world state member
      obtain ⟨obs, residual, transition, _⟩ :=
        (successful_act_iff plant goal world state action next).mp (h world state member)
      exact ⟨obs, residual, transition⟩
    · intro obs world residual member
      obtain ⟨prior, member, transition⟩ := member
      obtain ⟨obs', residual', transition', success⟩ :=
        (successful_act_iff plant goal world prior action next).mp (h world prior member)
      have eqs : obs' = obs ∧ residual' = residual := by
        simpa using transition'.symm.trans transition
      rcases eqs with ⟨rfl, rfl⟩
      exact success
  · rintro ⟨enabled, continuations⟩ world state member
    obtain ⟨obs, residual, transition⟩ := enabled world state member
    apply (successful_act_iff plant goal world state action next).mpr
    exact ⟨obs, residual, transition,
      continuations obs world residual ⟨state, member, transition⟩⟩

/-- A transition-invariant failure region rules out every policy, not merely
straight-line programs of a chosen length. -/
theorem invariant_excludes_success (plant : Plant World State Action Obs)
    (goal invariant : World → State → Prop)
    (preserved : ∀ world state action obs residual, invariant world state →
      plant.step world state action = some (obs, residual) → invariant world residual)
    (disjoint : ∀ world state, invariant world state → ¬ goal world state)
    (policy : Policy Action Obs) (world : World) (state : State)
    (initial : invariant world state) : ¬ Successful plant goal world state policy := by
  rintro ⟨residual, execution, success⟩
  exact disjoint world residual
    (policy.run_preserves plant invariant preserved world state residual initial execution) success

end Generic

namespace Specimen

/-- The specimen has either not been used, been lost, or become the target. -/
inductive State
  | fresh | spent | success
  deriving DecidableEq

instance : Fintype State :=
  ⟨{.fresh, .spent, .success}, by intro state; cases state <;> simp⟩

/-- Idle is included to allow arbitrarily many uninformative native steps. -/
inductive Action
  | idle | test | build (design : Bool)
  deriving DecidableEq

instance : Fintype Action :=
  ⟨{.idle, .test, .build false, .build true}, by
    intro action
    cases action with
    | idle => simp
    | test => simp
    | build design => cases design <;> simp⟩

inductive Obs
  | tick | bit (value : Bool)
  deriving DecidableEq

instance : Fintype Obs :=
  ⟨{.tick, .bit false, .bit true}, by
    intro obs
    cases obs with
    | tick => simp
    | bit value => cases value <;> simp⟩

/-- Both builds and the test are enabled in both worlds while the specimen is
fresh. Test output is exact; only its resource effect depends on `destructive`.
Neither failure nor target creation allows a second specimen to be obtained. -/
def plant (destructive : Bool) : Plant Bool State Action Obs where
  step world state action := match action with
    | .idle => some (.tick, state)
    | .test => match state with
      | .fresh => some (.bit world, if destructive then .spent else .fresh)
      | _ => none
    | .build design => match state with
      | .fresh => some (.tick, if world = design then .success else .spent)
      | _ => none

def goal (_ : Bool) (state : State) : Prop := state = .success

def initialBelief : Set (Bool × State) := {pair | pair.2 = .fresh}

def build (design : Bool) : Policy Action Obs := .act (.build design) (fun _ => .halt)

def diagnoseThenBuild : Policy Action Obs :=
  .act .test (fun obs => match obs with
    | .bit design => build design
    | .tick => .halt)

/-- The initial information does not reveal the world. -/
theorem both_worlds_initial :
    (false, State.fresh) ∈ initialBelief ∧ (true, State.fresh) ∈ initialBelief := by
  constructor <;> rfl

/-- No enabledness oracle secretly gives away the design. -/
theorem every_initial_action_enabled (destructive : Bool) (action : Action) :
    Enabled (plant destructive) initialBelief action := by
  intro world state member
  have hs : state = .fresh := member
  subst state
  cases action <;> simp [plant]

/-- A matching build succeeds from fresh stock in each separately known world. -/
theorem worldwise_build (destructive world : Bool) :
    Successful (plant destructive) goal world .fresh (build world) := by
  exact ⟨.success, by simp [build, Policy.run, plant], rfl⟩

/-- An exact one-step native diagnostic, including its actual resource effect. -/
theorem perfect_test (destructive world : Bool) :
    (plant destructive).step world .fresh .test =
      some (.bit world, if destructive then .spent else .fresh) := rfl

/-- The revised belief exactly identifies the original hidden world, but keeps
its residual stock. The nondestructive and destructive cases use the same filter. -/
theorem test_update (destructive observed : Bool) :
    update (plant destructive) initialBelief .test (.bit observed) =
      {(observed, if destructive then State.spent else State.fresh)} := by
  ext ⟨world, state⟩
  simp only [update, initialBelief, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  simp [plant, Prod.ext_iff, eq_comm]

/-- Once the specimen is lost, every permitted transition keeps it lost. -/
theorem spent_preserved (destructive world : Bool) (state : State)
    (action : Action) (obs : Obs) (residual : State)
    (h : state = .spent)
    (transition : (plant destructive).step world state action = some (obs, residual)) :
    residual = .spent := by
  subst state
  cases action <;> simp [plant] at transition
  exact transition.2.symm

theorem spent_never_succeeds (destructive world : Bool) (policy : Policy Action Obs) :
    ¬ Successful (plant destructive) goal world .spent policy := by
  apply invariant_excludes_success (plant destructive) goal
    (fun _ state => state = .spent)
  · exact spent_preserved destructive
  · intro world state h
    simp [goal, h]
  · rfl

/-- Every finite observation-based policy has a failing initial world. The
induction includes arbitrarily many idle actions and every observation branch. -/
theorem destructive_policy_fails (policy : Policy Action Obs) :
    ∃ world, ¬ Successful (plant true) goal world .fresh policy := by
  induction policy with
  | halt =>
      exact ⟨false, by simp [Successful, Policy.run, goal]⟩
  | act action next ih =>
      cases action with
      | idle =>
          obtain ⟨world, failure⟩ := ih .tick
          refine ⟨world, ?_⟩
          simpa [successful_act_iff, plant] using failure
      | test =>
          refine ⟨false, ?_⟩
          simpa [successful_act_iff, plant] using
            spent_never_succeeds true false (next (.bit false))
      | build design =>
          refine ⟨!design, ?_⟩
          cases design <;> simpa [successful_act_iff, plant] using
            spent_never_succeeds true _ (next .tick)

theorem no_uniform_destructive_policy :
    ¬ ∃ policy, UniformSuccess (plant true) goal initialBelief policy := by
  rintro ⟨policy, uniform⟩
  obtain ⟨world, failure⟩ := destructive_policy_fails policy
  exact failure (uniform world .fresh rfl)

/-- Even exact posterior knowledge cannot restore the consumed specimen. -/
theorem destructive_posterior_infeasible (observed : Bool) :
    ¬ ∃ policy, UniformSuccess (plant true) goal
      (update (plant true) initialBelief .test (.bit observed)) policy := by
  rw [test_update]
  rintro ⟨policy, uniform⟩
  exact spent_never_succeeds true observed policy
    (uniform observed .spent (by simp))

/-- The very same two-action observation policy succeeds when diagnosis retains
fresh stock. Its build choice is made by the returned bit, not the hidden world. -/
theorem nondestructive_repair :
    UniformSuccess (plant false) goal initialBelief diagnoseThenBuild := by
  intro world state member
  have hs : state = .fresh := member
  subst state
  refine ⟨.success, ?_, rfl⟩
  simp [diagnoseThenBuild, build, Policy.run, plant]

/-- A compact statement of the invalid compositional inference. -/
theorem diagnosis_and_worldwise_construction_do_not_compose :
    (∀ world, ∃ policy, Successful (plant true) goal world .fresh policy) ∧
    (∀ world, (plant true).step world .fresh .test = some (.bit world, .spent)) ∧
    (∀ observed, update (plant true) initialBelief .test (.bit observed) =
      {(observed, State.spent)}) ∧
    (¬ ∃ policy, UniformSuccess (plant true) goal initialBelief policy) := by
  exact ⟨fun world => ⟨build world, worldwise_build true world⟩,
    perfect_test true, test_update true, no_uniform_destructive_policy⟩

end Specimen
end ResourceSensitiveLoop

#print axioms ResourceSensitiveLoop.Policy.run_append
#print axioms ResourceSensitiveLoop.Policy.run_preserves
#print axioms ResourceSensitiveLoop.uniform_act_iff
#print axioms ResourceSensitiveLoop.Specimen.test_update
#print axioms ResourceSensitiveLoop.Specimen.destructive_policy_fails
#print axioms ResourceSensitiveLoop.Specimen.no_uniform_destructive_policy
#print axioms ResourceSensitiveLoop.Specimen.destructive_posterior_infeasible
#print axioms ResourceSensitiveLoop.Specimen.nondestructive_repair
#print axioms ResourceSensitiveLoop.Specimen.diagnosis_and_worldwise_construction_do_not_compose
