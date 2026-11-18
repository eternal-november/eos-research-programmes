import Std

/-!
Elementary foundations for Byzantine control research.

The results below check their stated logical and finite-model claims. They do not formalize a BFT protocol, a physical plant, distributed synthesis, or a cryptographic implementation. `decide` uses kernel-checked reduction; no `native_decide`, domain axioms, or unfinished proofs are used.
-/

namespace ByzantineControl

def Wins {Policy Environment : Type} (allowed : Environment → Prop)
    (satisfies : Policy → Environment → Prop) : Prop :=
  ∃ policy, ∀ environment, allowed environment → satisfies policy environment

theorem winning_antitone {Policy Environment : Type}
    (small large : Environment → Prop)
    (satisfies : Policy → Environment → Prop)
    (included : ∀ e, small e → large e) :
    Wins large satisfies → Wins small satisfies := by
  intro h
  obtain ⟨policy, hp⟩ := h
  exact ⟨policy, fun e he => hp e (included e he)⟩

theorem coalitionwise_is_not_uniform :
    (∀ b : Bool, ∃ a : Bool, a = b) ∧
    ¬ (∃ a : Bool, ∀ b : Bool, a = b) := by
  decide

def PermittedChoice (world action : Fin 3) : Prop := action ≠ world

theorem pairwise_is_not_joint :
    (∀ x y : Fin 3, ∃ a : Fin 3, PermittedChoice x a ∧ PermittedChoice y a) ∧
    ¬ (∃ a : Fin 3, ∀ x : Fin 3, PermittedChoice x a) := by
  unfold PermittedChoice
  decide

theorem uniform_policy_iff {State Observation Action : Type}
    (observe : State → Observation) (safeAction : State → Action → Prop) :
    (∃ policy : Observation → Action, ∀ x, safeAction x (policy (observe x))) ↔
    (∀ o, ∃ a, ∀ x, observe x = o → safeAction x a) := by
  constructor
  · rintro ⟨policy, hp⟩ o
    refine ⟨policy o, ?_⟩
    intro x hx
    simpa [hx] using hp x
  · intro h
    classical
    refine ⟨fun o => Classical.choose (h o), ?_⟩
    intro x
    exact Classical.choose_spec (h (observe x)) x rfl

def NonblockingSafe {State Action : Type} (next : State → Action → State → Prop)
    (target : State → Prop) (x : State) (a : Action) : Prop :=
  (∃ y, next x a y) ∧ ∀ y, next x a y → target y

theorem empty_successors_are_not_nonblocking {State Action : Type}
    (target : State → Prop) (x : State) (a : Action) :
    ¬ NonblockingSafe (fun (_ : State) (_ : Action) (_ : State) => False) target x a := by
  rintro ⟨⟨_, impossible⟩, _⟩
  exact impossible

theorem invariant_induction {State : Type}
    (safe : State → Prop) (next : State → State → Prop)
    (run : Nat → State) (initial : safe (run 0))
    (execution : ∀ t, next (run t) (run (t + 1)))
    (preserves : ∀ x y, safe x → next x y → safe y) :
    ∀ t, safe (run t) := by
  intro t
  induction t with
  | zero => exact initial
  | succ t ih => exact preserves (run t) (run (t + 1)) ih (execution t)

theorem envelope_step {State Info Action : Type}
    (contains : Info → State → Prop)
    (next : State → Action → State → Prop)
    (post : Info → Action → State → Prop) (safe : State → Prop)
    (information : Info) (x y : State) (action : Action)
    (coverage : contains information x)
    (realized : next x action y)
    (overapproximation : ∀ s t, contains information s → next s action t → post information action t)
    (certificate : ∀ t, post information action t → safe t) :
    safe y := by
  exact certificate y (overapproximation x y coverage realized)

def Knows {World Observation : Type}
    (observe : World → Observation) (fact : World → Prop) (w : World) : Prop :=
  ∀ v, observe v = observe w → fact v

theorem same_external_view_does_not_identify_reading :
    ¬ Knows (fun (_ : Bool) => ()) (fun reading => reading = true) true := by
  unfold Knows
  decide

theorem evidence_monotone {World : Type}
    (before after fact : World → Prop)
    (refines : ∀ w, after w → before w) :
    (∀ w, before w → fact w) → (∀ w, after w → fact w) := by
  intro known w hw
  exact known w (refines w hw)

theorem more_worlds_weaken_knowledge {World : Type}
    (small large fact : World → Prop)
    (included : ∀ w, small w → large w) :
    (∀ w, large w → fact w) → (∀ w, small w → fact w) := by
  intro known w hw
  exact known w (included w hw)

/- The next result assumes the cardinality inequality for a union; it checks only the arithmetic consequence, not the set-theoretic inequality or any protocol invariant. -/
theorem quorum_intersection_arithmetic (f n q₁ q₂ overlap : Nat)
    (population : n = 3 * f + 1)
    (first : 2 * f + 1 ≤ q₁) (second : 2 * f + 1 ≤ q₂)
    (unionBound : q₁ + q₂ ≤ n + overlap) : f < overlap := by
  omega

/- This is a single threshold gate with correct parties willing and able to authorize and Byzantine parties able to withhold. It is not a Byzantine agreement threshold. -/
theorem threshold_gate_feasible (n f : Nat) :
    (∃ q : Nat, f < q ∧ q + f ≤ n) ↔ 2 * f < n := by
  constructor
  · rintro ⟨q, hq, hn⟩
    omega
  · intro h
    exact ⟨f + 1, by omega, by omega⟩

namespace ContinuationCounterexample

abbrev State := Fin 6
abbrev Action := Fin 3

/- States 0,1 are initial alternatives; 2,3 are their successors; 4 is safe absorbing and 5 is unsafe absorbing. Actions 0,1,2 mean wait, left, right. Both initial states have the same observation, as do states 2 and 3. -/
def next (x : State) (a : Action) : State :=
  if x = 0 then (if a = 0 then 2 else 5)
  else if x = 1 then (if a = 0 then 3 else 5)
  else if x = 2 then (if a = 1 then 4 else 5)
  else if x = 3 then (if a = 2 then 4 else 5)
  else x

def safe (x : State) : Prop := x ≠ 5

def fullInformationPolicy (x : State) : Action :=
  if x = 2 then 1 else if x = 3 then 2 else 0

def initial (hidden : Bool) : State := if hidden then 1 else 0

theorem full_information_closed :
    ∀ x : State, safe x → safe (next x (fullInformationPolicy x)) := by
  unfold safe
  decide

theorem uniform_first_step :
    ∀ hidden : Bool, safe (next (initial hidden) 0) := by
  unfold safe
  decide

theorem no_uniform_two_step_plan :
    ¬ (∃ a b : Action, ∀ hidden : Bool,
      safe (next (initial hidden) a) ∧ safe (next (next (initial hidden) a) b)) := by
  unfold safe
  decide

end ContinuationCounterexample

#print axioms winning_antitone
#print axioms coalitionwise_is_not_uniform
#print axioms pairwise_is_not_joint
#print axioms uniform_policy_iff
#print axioms empty_successors_are_not_nonblocking
#print axioms invariant_induction
#print axioms envelope_step
#print axioms same_external_view_does_not_identify_reading
#print axioms evidence_monotone
#print axioms more_worlds_weaken_knowledge
#print axioms quorum_intersection_arithmetic
#print axioms threshold_gate_feasible
#print axioms ContinuationCounterexample.full_information_closed
#print axioms ContinuationCounterexample.uniform_first_step
#print axioms ContinuationCounterexample.no_uniform_two_step_plan

end ByzantineControl
