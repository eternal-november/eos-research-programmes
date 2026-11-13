import Mathlib

/-!
# Capability growth inside a supplied finite-premise operational grammar

This file isolates a precise, resource-relative sense of endogenous growth.
A rule declares a capability which can be produced after all its finite
prerequisites are retained. `Reachable` is the least closure under those rules.
It records finite derivations, not new physics or rules inferred from evidence.
The finite saturation implementation computes this closure when both the
capability universe and the rule presentation are finite.

No resource consumption, failure, probabilistic behavior, cost, or native
implementation is implicit: these are persistent, reusable capabilities.
-/

namespace EndogenousGrowth

universe u v

/-- An enabling rule has finitely many persistent prerequisites and one output. -/
structure Rule (α : Type u) where
  premises : Finset α
  conclusion : α
  deriving DecidableEq

/-- A finite derivation from retained resources, using the supplied rules. -/
inductive Reachable {α : Type u} (rules : Set (Rule α)) (seed : Set α) : α → Prop
  | initial {a} : a ∈ seed → Reachable rules seed a
  | fire {r} : r ∈ rules →
      (∀ a ∈ r.premises, Reachable rules seed a) → Reachable rules seed r.conclusion

/-- A proof-relevant construction plan. Unlike a proposition of feasibility,
this tree can be interpreted into supplied executable implementations. -/
inductive Plan {α : Type u} (rules : Set (Rule α)) (seed : Set α) : α → Type u
  | initial {a} : a ∈ seed → Plan rules seed a
  | fire {r} : r ∈ rules →
      (∀ a ∈ r.premises, Plan rules seed a) → Plan rules seed r.conclusion

namespace Plan

/-- Execute a finite plan in any native witness family. Supplying these rule
implementations is an independent obligation; closure does not create them.
The interpreter permits persistent reuse of seed implementations. -/
def run {α : Type u} {rules : Set (Rule α)} {seed : Set α}
    {Implementation : α → Type v}
    (start : ∀ a ∈ seed, Implementation a)
    (execute : ∀ r ∈ rules,
      (∀ a ∈ r.premises, Implementation a) → Implementation r.conclusion)
    {a : α} (plan : Plan rules seed a) : Implementation a :=
  match plan with
  | .initial h => start _ h
  | .fire hr children => execute _ hr (fun a ha => run start execute (children a ha))

theorem reachable {α : Type u} {rules : Set (Rule α)} {seed : Set α}
    {a : α} (plan : Plan rules seed a) : Reachable rules seed a := by
  induction plan with
  | initial h => exact Reachable.initial h
  | fire hr _ ih => exact Reachable.fire hr ih

end Plan

/-- Reachability has a finite proof-relevant construction plan. This existence
proof uses choice; it is not a claim that arbitrary infinite rule sets can be
searched effectively. The finite saturation algorithm below decides the
finite presentation case. -/
theorem reachable_iff_nonempty_plan {α : Type u} {rules : Set (Rule α)}
    {seed : Set α} {a : α} : Reachable rules seed a ↔ Nonempty (Plan rules seed a) := by
  constructor
  · intro h
    induction h with
    | initial hs => exact ⟨Plan.initial hs⟩
    | fire hr _ ih =>
        classical
        exact ⟨Plan.fire hr (fun a ha => Classical.choice (ih a ha))⟩
  · rintro ⟨p⟩
    exact p.reachable

/-- The complete finite-program capability repertoire. -/
def closure {α : Type u} (rules : Set (Rule α)) (seed : Set α) : Set α :=
  {a | Reachable rules seed a}

/-- A repertoire already closed under every declared enabling rule. -/
def Closed {α : Type u} (rules : Set (Rule α)) (s : Set α) : Prop :=
  ∀ r ∈ rules, (↑r.premises : Set α) ⊆ s → r.conclusion ∈ s

variable {α : Type u} {β : Type v}
variable {rules rules' : Set (Rule α)} {s t : Set α}

theorem seed_subset_closure : s ⊆ closure rules s := by
  intro a ha
  exact Reachable.initial ha

theorem closure_closed : Closed rules (closure rules s) := by
  intro r hr hp
  exact Reachable.fire hr hp

/-- Rule induction is a general impossibility principle: invariant sets bound
all finite capability-producing procedures in this grammar. -/
theorem closure_least (hs : s ⊆ t) (ht : Closed rules t) : closure rules s ⊆ t := by
  intro a ha
  induction ha with
  | initial h => exact hs h
  | fire hr _ ih => exact ht _ hr ih

theorem closure_mono (h : s ⊆ t) : closure rules s ⊆ closure rules t :=
  closure_least (Set.Subset.trans h seed_subset_closure) closure_closed

theorem closure_rules_mono (h : rules ⊆ rules') : closure rules s ⊆ closure rules' s := by
  apply closure_least seed_subset_closure
  intro r hr hp
  exact Reachable.fire (h hr) hp

@[simp] theorem closure_idempotent : closure rules (closure rules s) = closure rules s := by
  apply Set.Subset.antisymm
  · exact closure_least (Set.Subset.refl _) closure_closed
  · exact seed_subset_closure

/-- A completely closed baseline admits no novelty relative to that same
baseline. Strict staged growth must use a smaller current resource state. -/
theorem closure_eq_of_closed (h : Closed rules s) : closure rules s = s := by
  exact Set.Subset.antisymm (closure_least (Set.Subset.refl _) h) seed_subset_closure

theorem not_reachable_of_invariant {a : α} (hs : s ⊆ t) (ht : Closed rules t)
    (ha : a ∉ t) : a ∉ closure rules s := by
  exact fun h => ha (closure_least hs ht h)

/-- Adding only resources that were already derivable does not enlarge the
complete closure, even when those resources shorten later procedures. -/
theorem closure_derived_resources (h : t ⊆ closure rules s) :
    closure rules (s ∪ t) = closure rules s := by
  apply Set.Subset.antisymm
  · apply closure_least _ closure_closed
    exact Set.union_subset seed_subset_closure h
  · exact closure_mono Set.subset_union_left

/-- Joint use can enable more than either repertoire alone, but closing each
component before combining does not change the eventual joint repertoire. -/
theorem closure_union_closed :
    closure rules (closure rules s ∪ closure rules t) = closure rules (s ∪ t) := by
  apply Set.Subset.antisymm
  · apply closure_least _ closure_closed
    exact Set.union_subset
      (closure_mono Set.subset_union_left) (closure_mono Set.subset_union_right)
  · apply closure_mono
    exact Set.union_subset_union seed_subset_closure seed_subset_closure

/-- Resource-relative novelty has both a construction and an impossibility
obligation. This is not novelty relative to the full runtime language. -/
def StrictGain (rules : Set (Rule α)) (baseline acquired : Set α) : Prop :=
  ∃ a, a ∈ closure rules acquired ∧ a ∉ closure rules baseline

/-- A grammar with no nullary production cannot create a capability from
nothing. Every productive process needs a seed or an explicitly supplied
zero-input primitive. -/
theorem closure_empty_of_nonempty_premises
    (h : ∀ r ∈ rules, r.premises.Nonempty) : closure rules ∅ = ∅ := by
  apply closure_eq_of_closed
  intro r hr hp
  obtain ⟨a, ha⟩ := h r hr
  exact (hp ha).elim

/-- A general forward compiler need only realize source rules by target
*derivations*, not by one target primitive each. -/
structure Compiler (source : Set (Rule α)) (target : Set (Rule β)) where
  encode : α → β
  compile_rule : ∀ r ∈ source,
    encode r.conclusion ∈ closure target (encode '' (↑r.premises : Set α))

namespace Compiler

variable {source : Set (Rule α)} {target : Set (Rule β)}

/-- Primitive correctness extends to every finite derivation by substitution. -/
theorem preserves (c : Compiler source target) {seed : Set α} {a : α}
    (h : a ∈ closure source seed) : c.encode a ∈ closure target (c.encode '' seed) := by
  induction h with
  | initial hs =>
      exact Reachable.initial ⟨_, hs, rfl⟩
  | @fire r hr hp ih =>
      have hc := c.compile_rule r hr
      have sub : c.encode '' (↑r.premises : Set α) ⊆ closure target (c.encode '' seed) := by
        rintro _ ⟨x, hx, rfl⟩
        exact ih x hx
      have := closure_mono (rules := target) sub hc
      simpa only [closure_idempotent] using this

/-- The identity compilation uses each rule once after its premises. -/
def identity (rules : Set (Rule α)) : Compiler rules rules where
  encode := id
  compile_rule r hr := by
    apply Reachable.fire hr
    intro a ha
    exact Reachable.initial ⟨a, ha, rfl⟩

/-- General derivation compilers compose, including their substitution proofs. -/
def comp {γ : Type*} {last : Set (Rule γ)}
    (d : Compiler target last) (c : Compiler source target) : Compiler source last where
  encode := d.encode ∘ c.encode
  compile_rule r hr := by
    have h := d.preserves (c.compile_rule r hr)
    simpa only [Set.image_image, Function.comp_apply] using h

/-- Forward correctness alone does not preserve strict gaps. Reflection of
baseline realizability is the additional obligation needed here. -/
theorem preserves_strictGain (c : Compiler source target) {baseline acquired : Set α}
    (reflects : ∀ a, c.encode a ∈ closure target (c.encode '' baseline) →
      a ∈ closure source baseline)
    (h : StrictGain source baseline acquired) :
    StrictGain target (c.encode '' baseline) (c.encode '' acquired) := by
  obtain ⟨a, ha, hn⟩ := h
  exact ⟨c.encode a, c.preserves ha, fun hb => hn (reflects a hb)⟩

/-- No injectivity assumption is needed for forward correctness. A left inverse
plus a reverse compiler is one concrete sufficient condition for reflection. -/
theorem reflects_of_reverse (c : Compiler source target)
    (d : Compiler target source) (hleft : Function.LeftInverse d.encode c.encode)
    {seed : Set α} {a : α}
    (h : c.encode a ∈ closure target (c.encode '' seed)) : a ∈ closure source seed := by
  have hp := d.preserves h
  have he : d.encode '' (c.encode '' seed) = seed := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [hleft y] using hy
    · intro hx
      exact ⟨c.encode x, ⟨x, hx, rfl⟩, hleft x⟩
  simpa only [he, hleft a] using hp

end Compiler

/-! ## An executable finite saturation algorithm -/

section Finite

variable [DecidableEq α]

/-- One exhaustive round. Old resources persist; all enabled outputs are added. -/
def step (rules : Finset (Rule α)) (s : Finset α) : Finset α :=
  s ∪ rules.biUnion (fun r => if r.premises ⊆ s then {r.conclusion} else ∅)

def stages (rules : Finset (Rule α)) (seed : Finset α) : ℕ → Finset α
  | 0 => seed
  | n + 1 => step rules (stages rules seed n)

theorem mem_step {rules : Finset (Rule α)} {s : Finset α} {a : α} :
    a ∈ step rules s ↔ a ∈ s ∨ ∃ r ∈ rules, r.premises ⊆ s ∧ r.conclusion = a := by
  simp only [step, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (ha | ⟨r, hr, ha⟩)
    · exact Or.inl ha
    · right
      split_ifs at ha with hp
      · exact ⟨r, hr, hp, (Finset.mem_singleton.mp ha).symm⟩
      · simp at ha
  · rintro (ha | ⟨r, hr, hp, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨r, hr, by simp [hp]⟩

theorem subset_step (rules : Finset (Rule α)) (s : Finset α) : s ⊆ step rules s :=
  Finset.subset_union_left

theorem step_mono (rules : Finset (Rule α)) {s t : Finset α} (h : s ⊆ t) :
    step rules s ⊆ step rules t := by
  intro a ha
  rw [mem_step] at ha ⊢
  rcases ha with ha | ⟨r, hr, hp, he⟩
  · exact Or.inl (h ha)
  · exact Or.inr ⟨r, hr, Finset.Subset.trans hp h, he⟩

theorem stages_mono (rules : Finset (Rule α)) (seed : Finset α) :
    Monotone (stages rules seed) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_step rules _

theorem stages_sound (rules : Finset (Rule α)) (seed : Finset α) (n : ℕ) :
    (↑(stages rules seed n) : Set α) ⊆ closure (↑rules : Set (Rule α)) (↑seed : Set α) := by
  induction n with
  | zero => exact seed_subset_closure
  | succ n ih =>
      intro a ha
      change a ∈ step rules (stages rules seed n) at ha
      rw [mem_step] at ha
      rcases ha with ha | ⟨r, hr, hp, rfl⟩
      · exact ih ha
      · exact Reachable.fire hr (fun x hx => ih (hp hx))

theorem fixed_iff_closed (rules : Finset (Rule α)) (s : Finset α) :
    step rules s = s ↔ Closed (↑rules : Set (Rule α)) (↑s : Set α) := by
  constructor
  · intro he r hr hp
    have hm : r.conclusion ∈ step rules s := mem_step.mpr (Or.inr ⟨r, hr, hp, rfl⟩)
    change r.conclusion ∈ s
    simpa only [he] using hm
  · intro hc
    apply Finset.Subset.antisymm _ (subset_step rules s)
    intro a ha
    rcases mem_step.mp ha with ha | ⟨r, hr, hp, rfl⟩
    · exact ha
    · exact hc r hr hp

theorem stages_fixed_after (rules : Finset (Rule α)) (seed : Finset α) {n : ℕ}
    (h : stages rules seed (n + 1) = stages rules seed n) :
    ∀ m, stages rules seed (n + m) = stages rules seed n := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, stages, ih]
      exact h

/-- On a finite capability universe, saturation is fixed by `card α` rounds.
This is a worst-case mathematical bound, not a claim of practical efficiency. -/
theorem stages_stable [Fintype α] (rules : Finset (Rule α)) (seed : Finset α) :
    stages rules seed (Fintype.card α + 1) = stages rules seed (Fintype.card α) := by
  let f : ℕ → ℕ := fun n => (stages rules seed n).card
  have hm : Monotone f := fun i j hij => Finset.card_le_card (stages_mono rules seed hij)
  have hb : ∀ n, f n ≤ Fintype.card α := fun n => Finset.card_le_univ _
  have hs : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2) := by
    intro n hn
    have he : stages rules seed n = stages rules seed (n + 1) :=
      Finset.eq_of_subset_of_card_le (subset_step rules _) hn.symm.le
    have he' : stages rules seed (n + 1) = stages rules seed (n + 2) := by
      change step rules (stages rules seed n) = step rules (stages rules seed (n + 1))
      rw [he]
    exact congrArg Finset.card he'
  have hc : f (Fintype.card α + 1) = f (Fintype.card α) :=
    Nat.stabilises_of_monotone hm hb hs (Nat.le_succ _)
  exact (Finset.eq_of_subset_of_card_le (subset_step rules _) hc.le).symm

/-- Executable closure, with an explicit finite bound on the number of rounds. -/
def saturate [Fintype α] (rules : Finset (Rule α)) (seed : Finset α) : Finset α :=
  stages rules seed (Fintype.card α)

/-- The finite algorithm computes exactly finite derivability, with no oracle
for feasibility and no unbounded search hidden in its definition. -/
theorem saturate_correct [Fintype α] (rules : Finset (Rule α)) (seed : Finset α) :
    (↑(saturate rules seed) : Set α) = closure (↑rules : Set (Rule α)) (↑seed : Set α) := by
  apply Set.Subset.antisymm
  · exact stages_sound rules seed _
  · apply closure_least
    · exact stages_mono rules seed (Nat.zero_le _)
    · apply (fixed_iff_closed rules _).mp
      exact stages_stable rules seed

end Finite

/-! ## A strict joint-resource construction with subsequent reuse -/

namespace JointExample

inductive Capability
  | left | right | assembled | result
  deriving DecidableEq

instance : Fintype Capability where
  elems := {Capability.left, Capability.right, Capability.assembled, Capability.result}
  complete a := by cases a <;> simp

open Capability

def assemble : Rule Capability := ⟨{left, right}, assembled⟩
def useAssembly : Rule Capability := ⟨{assembled}, result⟩
def productionRules : Finset (Rule Capability) := {assemble, useAssembly}

def leftSeed : Finset Capability := {left}
def rightSeed : Finset Capability := {right}
def jointSeed : Finset Capability := {left, right}

/-- Neither separate resource enables production on its own. -/
theorem left_saturation : saturate productionRules leftSeed = leftSeed := by decide
theorem right_saturation : saturate productionRules rightSeed = rightSeed := by decide

/-- Combining resources constructs a new capability which enables a further
operation. Both stages execute within the same initially declared grammar. -/
theorem joint_saturation : saturate productionRules jointSeed = Finset.univ := by decide

theorem strict_compositional_gain :
    result ∈ closure (↑productionRules : Set (Rule Capability)) (↑jointSeed : Set Capability) ∧
    result ∉ closure (↑productionRules : Set (Rule Capability)) (↑leftSeed : Set Capability) ∧
    result ∉ closure (↑productionRules : Set (Rule Capability)) (↑rightSeed : Set Capability) := by
  simp only [← saturate_correct, left_saturation, right_saturation, joint_saturation]
  decide

/-- Closing the components separately and merely taking their union misses
this joint capability. Joint interaction, not a label wrapper, matters. -/
theorem strict_joint_not_union :
    closure (↑productionRules : Set (Rule Capability)) (↑leftSeed : Set Capability) ∪
      closure (↑productionRules : Set (Rule Capability)) (↑rightSeed : Set Capability) ⊂
    closure (↑productionRules : Set (Rule Capability)) (↑jointSeed : Set Capability) := by
  constructor
  · apply Set.union_subset
    · exact closure_mono (by change leftSeed ⊆ jointSeed; decide)
    · exact closure_mono (by change rightSeed ⊆ jointSeed; decide)
  · intro h
    have hmem := h strict_compositional_gain.1
    rcases hmem with hl | hr
    · exact strict_compositional_gain.2.1 hl
    · exact strict_compositional_gain.2.2 hr

/-- The initial stages are strictly increasing, without any rule being added. -/
theorem two_strict_stages :
    stages productionRules jointSeed 0 ⊂ stages productionRules jointSeed 1 ∧
    stages productionRules jointSeed 1 ⊂ stages productionRules jointSeed 2 := by decide

end JointExample

/-! ## Why a correct forward compiler alone cannot preserve novelty -/

namespace CompilerCounterexample

/-- The source has two independent capabilities and no enabling rules. -/
def source : Set (Rule Bool) := ∅
/-- The target has one capability and no enabling rules. -/
def target : Set (Rule Unit) := ∅

/-- A perfectly sound compiler can forget distinctions. -/
def collapse : Compiler source target where
  encode _ := ()
  compile_rule _ h := False.elim h

theorem source_gap : StrictGain source {false} {false, true} := by
  refine ⟨true, Reachable.initial (by simp), ?_⟩
  apply not_reachable_of_invariant (t := {false}) (Set.Subset.refl _) ?_ (by simp)
  intro _ h
  exact False.elim h

/-- The source strict gain vanishes after a correct forward translation. -/
theorem no_target_gap :
    ¬ StrictGain target (collapse.encode '' {false}) (collapse.encode '' {false, true}) := by
  rintro ⟨a, ha, hn⟩
  apply hn
  apply Reachable.initial
  cases a
  exact ⟨false, by simp, rfl⟩

/-- Even an injective identity-on-capabilities compiler can lose a gap if the
target baseline has additional native ways to produce the encoded output. -/
def extraRule : Rule Bool := ⟨{false}, true⟩
def expandedTarget : Set (Rule Bool) := {extraRule}
def inclusion : Compiler source expandedTarget where
  encode := id
  compile_rule _ h := False.elim h

theorem inclusion_injective : Function.Injective inclusion.encode := fun _ _ h => h

theorem expanded_baseline_all : closure expandedTarget {false} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  cases a with
  | false => exact Reachable.initial (by simp)
  | true =>
      apply Reachable.fire (r := extraRule) (by simp [expandedTarget])
      intro a ha
      have he : a = false := by simpa [extraRule] using ha
      subst a
      exact Reachable.initial (by simp)

theorem no_injective_target_gap :
    ¬ StrictGain expandedTarget (inclusion.encode '' {false})
      (inclusion.encode '' {false, true}) := by
  rintro ⟨a, _, hn⟩
  apply hn
  have he : inclusion.encode '' ({false} : Set Bool) = {false} := by
    simp [inclusion]
  rw [he, expanded_baseline_all]
  trivial

end CompilerCounterexample

#print axioms reachable_iff_nonempty_plan
#print axioms Plan.run
#print axioms closure_least
#print axioms Compiler.preserves
#print axioms Compiler.preserves_strictGain
#print axioms Compiler.reflects_of_reverse
#print axioms saturate_correct
#print axioms JointExample.strict_joint_not_union
#print axioms JointExample.two_strict_stages
#print axioms CompilerCounterexample.no_target_gap
#print axioms CompilerCounterexample.no_injective_target_gap

end EndogenousGrowth
