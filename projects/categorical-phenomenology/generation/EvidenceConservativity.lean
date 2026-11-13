import GeneratedTests
import Mathlib.Data.Set.Card
import Mathlib.Order.Monotone.Basic

/-!
# Evidence-relative structural certificates and uniform reconstruction

`E` is a set of admissible worlds. Incidence and the proposed new column may
both depend on the world. All carriers may be empty or infinite. Conclusions
about an actual world require its membership in `E`; consistency is not inferred.
The object-side nerve uses finite nonempty faces, as in `GeneratedTests`.

The main non-definitional additions are:
* guaranteed consequence (the intersection of worldwise FCA closures) is a
  closure operator, and it grows when evidence excludes worlds;
* on finite H, simultaneous worldwise closure stabilizes by |H| steps and
  gives the least common-closed hull, with the opposite evidence order;
* an exact criterion for a single conjunction of old labels to define a
  world-dependent column uniformly over the evidence;
* explicit finite counterexamples separating worldwise structural safety,
  guaranteed consequences, must-incidence, and uniform reconstruction.

No physical execution, evidence acquisition, or topological realization is
formalized. `E` and the semantic world family are supplied parameters.
-/

namespace EvidenceConservativity

open GeneratedTests

universe u v w
variable {W : Type u} {H : Type v} {T : Type w}

/-- Adding C preserves the full FCA closure in every admissible world. -/
def ClosurePreserved (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) : Prop :=
  ∀ ω, ω ∈ E → closure (addAttribute (R ω) (C ω)) = closure (R ω)

/-- Adding C preserves all finite nonempty object-side faces in every world. -/
def NervePreserved (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) : Prop :=
  ∀ ω, ω ∈ E → ∀ A : Set H, A.Finite → A.Nonempty →
    (hasWitness (addAttribute (R ω) (C ω)) A ↔ hasWitness (R ω) A)

/-- Both literal closure and finite nonempty face preservation. -/
def Conservative (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) : Prop :=
  ClosurePreserved E R C ∧ NervePreserved E R C

theorem closurePreserved_iff (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) :
    ClosurePreserved E R C ↔ ∀ ω, ω ∈ E → closure (R ω) (C ω) = C ω := by
  constructor
  · intro h ω hω
    exact (addAttribute_closure_operator_eq_iff (R ω) (C ω)).mp (h ω hω)
  · intro h ω hω
    exact (addAttribute_closure_operator_eq_iff (R ω) (C ω)).mpr (h ω hω)

/-- No finiteness hypothesis on a new column is needed for this criterion. -/
theorem nervePreserved_iff (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) :
    NervePreserved E R C ↔
      ∀ ω, ω ∈ E → ∀ A : Set H, A.Finite → A.Nonempty → A ⊆ C ω →
        hasWitness (R ω) A := by
  constructor
  · intro h ω hω A hfin hne hsub
    exact (h ω hω A hfin hne).mp
      ((hasWitness_addAttribute_iff (R ω) (C ω) A).mpr (Or.inr hsub))
  · intro h ω hω A hfin hne
    rw [hasWitness_addAttribute_iff]
    constructor
    · rintro (hw | hsub)
      · exact hw
      · exact h ω hω A hfin hne hsub
    · exact Or.inl

theorem conservative_iff_finite (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) (hfinite : ∀ ω, ω ∈ E → (C ω).Finite) :
    Conservative E R C ↔
      ∀ ω, ω ∈ E → closure (R ω) (C ω) = C ω ∧
        ((C ω).Nonempty → hasWitness (R ω) (C ω)) := by
  constructor
  · rintro ⟨hc, hn⟩ ω hω
    refine ⟨(closurePreserved_iff E R C).mp hc ω hω, ?_⟩
    exact (finite_nonempty_nerve_unchanged_iff (R ω) (C ω) (hfinite ω hω)).mp
      (hn ω hω)
  · intro h
    constructor
    · exact (closurePreserved_iff E R C).mpr (fun ω hω => (h ω hω).1)
    · intro ω hω
      exact (finite_nonempty_nerve_unchanged_iff (R ω) (C ω) (hfinite ω hω)).mpr
        (h ω hω).2

/-- More evidence removes admissible worlds and cannot invalidate this certificate. -/
theorem conservative_restrict {E F : Set W} (hFE : F ⊆ E)
    (R : W → H → T → Prop) (C : W → Set H) :
    Conservative E R C → Conservative F R C := by
  rintro ⟨hc, hn⟩
  exact ⟨fun ω hω => hc ω (hFE hω), fun ω hω => hn ω (hFE hω)⟩

/-- Inconsistent evidence certifies everything vacuously, so it is not validation. -/
theorem conservative_empty (R : W → H → T → Prop) (C : W → Set H) :
    Conservative ∅ R C := by
  constructor <;> intro ω hω <;> exact False.elim hω

/-- Conditional soundness at the actual world, with the membership premise explicit. -/
theorem conservative_at_actual {E : Set W} (R : W → H → T → Prop)
    (C : W → Set H) (h : Conservative E R C) {actual : W} (ha : actual ∈ E) :
    closure (addAttribute (R actual) (C actual)) = closure (R actual) ∧
    ∀ A : Set H, A.Finite → A.Nonempty →
      (hasWitness (addAttribute (R actual) (C actual)) A ↔ hasWitness (R actual) A) :=
  ⟨h.1 actual ha, h.2 actual ha⟩

/-- Observation equality after every declared transition/readout map.
No composition laws are needed for preservation of this relation. -/
def futureEquivalent {M : Type*} (R : H → T → Prop) (τ : M → H → H)
    (h k : H) : Prop := ∀ m t, R (τ m h) t ↔ R (τ m k) t

theorem closed_extent_cannot_split_rows (R : H → T → Prop) (C : Set H)
    (hc : closure R C = C) {h k : H} (hrows : ∀ t, R h t ↔ R k t) :
    h ∈ C ↔ k ∈ C := by
  constructor
  · intro hh
    have hk : k ∈ closure R C := fun t ht => (hrows t).mp (ht h hh)
    rwa [hc] at hk
  · intro hk
    have hh : h ∈ closure R C := fun t ht => (hrows t).mpr (ht k hk)
    rwa [hc] at hh

/-- Worldwise FCA preservation also preserves all future-observation equality,
for the same prescribed transition maps in the original and extended context. -/
theorem closurePreserved_futureEquivalent {M : Type*}
    (E : Set W) (R : W → H → T → Prop) (C : W → Set H)
    (τ : W → M → H → H) (hc : ClosurePreserved E R C) :
    ∀ ω, ω ∈ E → ∀ h k,
      futureEquivalent (addAttribute (R ω) (C ω)) (τ ω) h k ↔
      futureEquivalent (R ω) (τ ω) h k := by
  intro ω hω h k
  constructor
  · intro heq m t
    exact heq m (some t)
  · intro heq m t
    cases t with
    | none =>
      exact closed_extent_cannot_split_rows (R ω) (C ω)
        ((closurePreserved_iff E R C).mp hc ω hω) (heq m)
    | some t => exact heq m t

/-- Consequences shared by all worlds, not closure under each world's consequences. -/
def guaranteedClosure (E : Set W) (R : W → H → T → Prop) (A : Set H) : Set H :=
  {h | ∀ ω, ω ∈ E → h ∈ closure (R ω) A}

theorem subset_guaranteedClosure (E : Set W) (R : W → H → T → Prop) (A : Set H) :
    A ⊆ guaranteedClosure E R A := by
  intro h hh ω _
  exact subset_closure (R ω) A hh

theorem guaranteedClosure_mono (E : Set W) (R : W → H → T → Prop)
    {A B : Set H} (hAB : A ⊆ B) :
    guaranteedClosure E R A ⊆ guaranteedClosure E R B := by
  intro h hh ω hω
  exact closure_mono (R ω) hAB (hh ω hω)

/-- The pointwise infimum of arbitrary FCA closures is again a closure operator. -/
theorem guaranteedClosure_idempotent (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    guaranteedClosure E R (guaranteedClosure E R A) = guaranteedClosure E R A := by
  apply Set.Subset.antisymm
  · intro h hh ω hω
    have hsub : guaranteedClosure E R A ⊆ closure (R ω) A :=
      fun _ hx => hx ω hω
    have hm := closure_mono (R ω) hsub (hh ω hω)
    rwa [closure_idempotent] at hm
  · exact subset_guaranteedClosure E R (guaranteedClosure E R A)

/-- Excluding worlds enlarges the guaranteed consequence closure. -/
theorem guaranteedClosure_restrict {E F : Set W} (hFE : F ⊆ E)
    (R : W → H → T → Prop) (A : Set H) :
    guaranteedClosure E R A ⊆ guaranteedClosure F R A := by
  intro h hh ω hω
  exact hh ω (hFE hω)

/-! ## Common fixed points: the opposite evidence order -/

/-- One simultaneous step adds all consequences from every admissible world.
The explicit A term gives the correct identity behavior for empty evidence. -/
def closureStep (E : Set W) (R : W → H → T → Prop) (A : Set H) : Set H :=
  {h | h ∈ A ∨ ∃ ω, ω ∈ E ∧ h ∈ closure (R ω) A}

def saturation (E : Set W) (R : W → H → T → Prop) (A : Set H) : ℕ → Set H
  | 0 => A
  | n + 1 => closureStep E R (saturation E R A n)

theorem subset_closureStep (E : Set W) (R : W → H → T → Prop) (A : Set H) :
    A ⊆ closureStep E R A := fun _ hh => Or.inl hh

theorem closureStep_mono (E : Set W) (R : W → H → T → Prop)
    {A B : Set H} (hAB : A ⊆ B) : closureStep E R A ⊆ closureStep E R B := by
  rintro h (ha | ⟨ω, hω, hh⟩)
  · exact Or.inl (hAB ha)
  · exact Or.inr ⟨ω, hω, closure_mono (R ω) hAB hh⟩

/-- The fixed points of this step are exactly the sets closed in every world. -/
theorem closureStep_fixed_iff (E : Set W) (R : W → H → T → Prop) (A : Set H) :
    closureStep E R A = A ↔ ∀ ω, ω ∈ E → closure (R ω) A = A := by
  constructor
  · intro h ω hω
    apply Set.Subset.antisymm
    · intro x hx
      have hs : x ∈ closureStep E R A := Or.inr ⟨ω, hω, hx⟩
      rwa [h] at hs
    · exact subset_closure (R ω) A
  · intro h
    apply Set.Subset.antisymm
    · rintro x (hx | ⟨ω, hω, hx⟩)
      · exact hx
      · rwa [h ω hω] at hx
    · exact subset_closureStep E R A

theorem saturation_mono (E : Set W) (R : W → H → T → Prop) (A : Set H) :
    Monotone (saturation E R A) :=
  monotone_nat_of_le_succ (fun n => subset_closureStep E R (saturation E R A n))

theorem saturation_le_closed (E : Set W) (R : W → H → T → Prop)
    {A B : Set H} (hAB : A ⊆ B) (hB : ∀ ω, ω ∈ E → closure (R ω) B = B) :
    ∀ n, saturation E R A n ⊆ B := by
  intro n
  induction n with
  | zero => exact hAB
  | succ n ih =>
    intro x hx
    have hs := closureStep_mono E R ih hx
    rwa [(closureStep_fixed_iff E R B).mpr hB] at hs

/-- On a finite object set, simultaneous closure stabilizes by |H| steps.
No finiteness assumption is imposed on worlds or labels. This is a mathematical
bound; deciding or enumerating the semantic step needs extra assumptions. -/
theorem saturation_stabilizes [Finite H] (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    saturation E R A (Nat.card H + 1) = saturation E R A (Nat.card H) := by
  let f : ℕ → ℕ := fun n => (saturation E R A n).ncard
  have hm : Monotone f := fun _ _ h => Set.ncard_le_ncard (saturation_mono E R A h)
  have hb : ∀ n, f n ≤ Nat.card H := fun _ => Set.ncard_le_card _
  have he : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2) := by
    intro n hn
    have hs : saturation E R A n = saturation E R A (n + 1) :=
      Set.eq_of_subset_of_ncard_le (saturation_mono E R A (Nat.le_succ n)) hn.ge
    exact congrArg Set.ncard (congrArg (closureStep E R) hs)
  have hc : f (Nat.card H + 1) = f (Nat.card H) :=
    Nat.stabilises_of_monotone hm hb he (Nat.le_succ _)
  exact (Set.eq_of_subset_of_ncard_le
    (saturation_mono E R A (Nat.le_succ _)) hc.le).symm

/-- The least superset closed in every admissible world, for finite H. -/
noncomputable def commonClosedHull [Finite H] (E : Set W)
    (R : W → H → T → Prop) (A : Set H) : Set H :=
  saturation E R A (Nat.card H)

theorem commonClosedHull_closed [Finite H] (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    ∀ ω, ω ∈ E → closure (R ω) (commonClosedHull E R A) = commonClosedHull E R A :=
  (closureStep_fixed_iff E R (commonClosedHull E R A)).mp
    (saturation_stabilizes E R A)

/-- Universal property: exactly the least robustly closed superset of A. -/
theorem commonClosedHull_least [Finite H] (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    A ⊆ commonClosedHull E R A ∧
    (∀ ω, ω ∈ E → closure (R ω) (commonClosedHull E R A) = commonClosedHull E R A) ∧
    ∀ B : Set H, A ⊆ B → (∀ ω, ω ∈ E → closure (R ω) B = B) →
      commonClosedHull E R A ⊆ B := by
  refine ⟨saturation_mono E R A (Nat.zero_le _), commonClosedHull_closed E R A, ?_⟩
  intro B hAB hB
  exact saturation_le_closed E R hAB hB (Nat.card H)

theorem commonClosedHull_fixed_iff [Finite H] (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    commonClosedHull E R A = A ↔ ∀ ω, ω ∈ E → closure (R ω) A = A := by
  constructor
  · intro h ω hω
    simpa [h] using commonClosedHull_closed E R A ω hω
  · intro h
    exact Set.Subset.antisymm
      ((commonClosedHull_least E R A).2.2 A (fun _ hx => hx) h)
      (commonClosedHull_least E R A).1

theorem commonClosedHull_mono [Finite H] (E : Set W) (R : W → H → T → Prop)
    {A B : Set H} (hAB : A ⊆ B) :
    commonClosedHull E R A ⊆ commonClosedHull E R B := by
  apply (commonClosedHull_least E R A).2.2
  · exact hAB.trans (commonClosedHull_least E R B).1
  · exact commonClosedHull_closed E R B

theorem commonClosedHull_idempotent [Finite H] (E : Set W) (R : W → H → T → Prop)
    (A : Set H) :
    commonClosedHull E R (commonClosedHull E R A) = commonClosedHull E R A :=
  (commonClosedHull_fixed_iff E R _).mpr (commonClosedHull_closed E R A)

/-- Unlike guaranteed consequences, the common closed hull shrinks when worlds
are removed. The two constructions encode different questions. -/
theorem commonClosedHull_restrict [Finite H] {E F : Set W} (hFE : F ⊆ E)
    (R : W → H → T → Prop) (A : Set H) :
    commonClosedHull F R A ⊆ commonClosedHull E R A := by
  apply (commonClosedHull_least F R A).2.2
  · exact (commonClosedHull_least E R A).1
  · intro ω hω
    exact commonClosedHull_closed E R A ω (hFE hω)

/-- The columns known to contain C in every admissible world. -/
def uniformColumns (E : Set W) (R : W → H → T → Prop) (C : W → Set H) : Set T :=
  {t | ∀ ω, ω ∈ E → ∀ h, h ∈ C ω → R ω h t}

/-- The strongest conjunction of labels that uniformly contains C. -/
def uniformHull (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) (ω : W) : Set H :=
  {h | ∀ t, t ∈ uniformColumns E R C → R ω h t}

/-- One fixed set of labels defines C in every admissible world. -/
def UniformConjunction (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) : Prop :=
  ∃ I : Set T, ∀ ω, ω ∈ E → C ω = {h | ∀ t, t ∈ I → R ω h t}

/-- Exact reconstruction criterion, with a canonical maximal choice of labels. -/
theorem uniformConjunction_iff (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) :
    UniformConjunction E R C ↔ ∀ ω, ω ∈ E → uniformHull E R C ω = C ω := by
  constructor
  · rintro ⟨I, hI⟩ ω hω
    apply Set.Subset.antisymm
    · intro h hh
      rw [hI ω hω]
      intro t ht
      apply hh t
      intro ω' hω' x hx
      rw [hI ω' hω'] at hx
      exact hx t ht
    · intro h hh t ht
      exact ht ω hω h hh
  · intro h
    exact ⟨uniformColumns E R C, fun ω hω => (h ω hω).symm⟩

/-- A uniform conjunction certificate is stronger than worldwise FCA preservation. -/
theorem uniformConjunction_closurePreserved (E : Set W) (R : W → H → T → Prop)
    (C : W → Set H) (hc : UniformConjunction E R C) : ClosurePreserved E R C := by
  apply (closurePreserved_iff E R C).mpr
  obtain ⟨I, hI⟩ := hc
  intro ω hω
  apply Set.Subset.antisymm
  · intro h hh
    rw [hI ω hω]
    intro t ht
    apply hh t
    intro x hx
    rw [hI ω hω] at hx
    exact hx t ht
  · exact subset_closure (R ω) (C ω)

/-- Must-incidence remembers only entries true in every admissible world. -/
def mustIncidence (E : Set W) (R : W → H → T → Prop) : H → T → Prop :=
  fun h t => ∀ ω, ω ∈ E → R ω h t

/-- A must-incidence witness is precisely one label that works in every world. -/
theorem mustIncidence_witness_iff (E : Set W) (R : W → H → T → Prop) (A : Set H) :
    hasWitness (mustIncidence E R) A ↔
      ∃ t, ∀ ω, ω ∈ E → ∀ h, h ∈ A → R ω h t := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun ω hω h hh => ht h hh ω hω⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, fun h hh ω hω => ht ω hω h hh⟩

theorem mustIncidence_witness_sound (E : Set W) (R : W → H → T → Prop)
    (A : Set H) (h : hasWitness (mustIncidence E R) A) :
    ∀ ω, ω ∈ E → hasWitness (R ω) A := by
  obtain ⟨t, ht⟩ := (mustIncidence_witness_iff E R A).mp h
  exact fun ω hω => ⟨t, ht ω hω⟩

/-! ## Finite correlated-world counterexamples -/

namespace Counterexample

/-- At each world, precisely the matching label has extent {true}. -/
def switchR (ω h t : Bool) : Prop := h = true ∧ t = ω

def switchC (_ : Bool) : Set Bool := {true}

theorem switch_closed (ω : Bool) : closure (switchR ω) (switchC ω) = switchC ω := by
  apply Set.Subset.antisymm
  · intro h hh
    exact (hh ω (fun x hx => ⟨hx, rfl⟩)).1
  · exact subset_closure (switchR ω) (switchC ω)

theorem switch_witness (ω : Bool) : hasWitness (switchR ω) (switchC ω) :=
  ⟨ω, fun _ hh => ⟨hh, rfl⟩⟩

/-- The added test is exactly one existing column in each world. -/
theorem switch_conservative : Conservative Set.univ switchR switchC := by
  apply (conservative_iff_finite Set.univ switchR switchC
    (fun _ _ => Set.finite_singleton true)).mpr
  exact fun ω _ => ⟨switch_closed ω, fun _ => switch_witness ω⟩

theorem switch_no_uniform_witness :
    ¬ hasWitness (mustIncidence Set.univ switchR) ({true} : Set Bool) := by
  rintro ⟨t, ht⟩
  have hfalse : t = false := (ht true rfl false (Set.mem_univ _)).2
  have htrue : t = true := (ht true rfl true (Set.mem_univ _)).2
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-- The must-incidence complex can lose faces present in every admissible world. -/
theorem robust_nerve_strictly_exceeds_must :
    (∀ ω : Bool, hasWitness (switchR ω) ({true} : Set Bool)) ∧
      ¬ hasWitness (mustIncidence Set.univ switchR) ({true} : Set Bool) :=
  ⟨switch_witness, switch_no_uniform_witness⟩

/-- No old label contains C uniformly over the two worlds. -/
theorem switch_uniformColumns_empty :
    uniformColumns Set.univ switchR switchC = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hfalse : t = false := (ht false (Set.mem_univ _) true rfl).2
  have htrue : t = true := (ht true (Set.mem_univ _) true rfl).2
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-- Worldwise conservative does not mean one old conjunction works uniformly. -/
theorem switch_no_uniform_conjunction :
    ¬ UniformConjunction Set.univ switchR switchC := by
  intro h
  have heq := (uniformConjunction_iff Set.univ switchR switchC).mp h false
    (Set.mem_univ _)
  have hf : false ∈ uniformHull Set.univ switchR switchC false := by
    intro t ht
    rw [switch_uniformColumns_empty] at ht
    exact False.elim ht
  rw [heq] at hf
  exact Bool.noConfusion hf

/-- This family has one universal column at world false and {true} at world true. -/
def mixedR (ω h : Bool) (_ : Unit) : Prop := ω = false ∨ h = true

/-- Shared consequences can be closed without being closed in every world. -/
theorem guaranteed_closed_not_worldwise :
    guaranteedClosure Set.univ mixedR ({true} : Set Bool) = {true} ∧
      closure (mixedR false) ({true} : Set Bool) ≠ {true} := by
  constructor
  · apply Set.Subset.antisymm
    · intro h hh
      have hx := hh true (Set.mem_univ _) () (fun _ hx => Or.inr hx)
      rcases hx with impossible | hg
      · exact Bool.noConfusion impossible
      · exact hg
    · exact subset_guaranteedClosure Set.univ mixedR {true}
  · intro h
    have hf : false ∈ closure (mixedR false) ({true} : Set Bool) := by
      intro _ _
      exact Or.inl rfl
    rw [h] at hf
    exact Bool.noConfusion hf

/-- Here the guaranteed closure fixes {true}, but the common-closed hull is all H. -/
theorem mixed_commonClosedHull_univ :
    commonClosedHull Set.univ mixedR ({true} : Set Bool) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro h
  have hh : h ∈ closure (mixedR false)
      (commonClosedHull Set.univ mixedR ({true} : Set Bool)) :=
    fun _ _ => Or.inl rfl
  rwa [commonClosedHull_closed Set.univ mixedR ({true} : Set Bool)
    false (Set.mem_univ _)] at hh

/-! A nondegenerate edge version: old columns are {0} and {0,1},
with the labels swapped between the two worlds; object 2 remains outside. -/

def edgeR (ω : Bool) (h : Fin 3) (t : Bool) : Prop :=
  h = 0 ∨ (h = 1 ∧ t = ω)

def edgeC : Set (Fin 3) := {h | h = 0 ∨ h = 1}

theorem edge_witness (ω : Bool) : hasWitness (edgeR ω) edgeC := by
  refine ⟨ω, ?_⟩
  intro h hh
  rcases hh with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ⟨h1, rfl⟩

theorem edge_closed (ω : Bool) : closure (edgeR ω) edgeC = edgeC := by
  apply Set.Subset.antisymm
  · intro h hh
    obtain ⟨t, ht⟩ := edge_witness ω
    have hx := hh t ht
    exact hx.elim Or.inl (fun hx => Or.inr hx.1)
  · exact subset_closure (edgeR ω) edgeC

/-- The fixed syntax p OR q denotes this same safe edge in both worlds. -/
theorem edge_disjunction (ω : Bool) :
    {h | edgeR ω h false ∨ edgeR ω h true} = edgeC := by
  ext h
  constructor
  · rintro ((h0 | ⟨h1, _⟩) | (h0 | ⟨h1, _⟩))
    · exact Or.inl h0
    · exact Or.inr h1
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (h0 | h1)
    · exact Or.inl (Or.inl h0)
    · cases ω with
      | false => exact Or.inl (Or.inr ⟨h1, rfl⟩)
      | true => exact Or.inr (Or.inr ⟨h1, rfl⟩)

theorem edge_conservative :
    Conservative Set.univ edgeR (fun _ => edgeC) := by
  apply (conservative_iff_finite Set.univ edgeR (fun _ => edgeC)
    (fun _ _ => Set.toFinite _)).mpr
  exact fun ω _ => ⟨edge_closed ω, fun _ => edge_witness ω⟩

/-- Must-incidence retains {0} in both columns, losing the guaranteed edge. -/
theorem edge_mustIncidence (h : Fin 3) (t : Bool) :
    mustIncidence Set.univ edgeR h t ↔ h = 0 := by
  constructor
  · intro hm
    rcases hm false (Set.mem_univ _) with h0 | ⟨_, ht0⟩
    · exact h0
    · rcases hm true (Set.mem_univ _) with h0 | ⟨_, ht1⟩
      · exact h0
      · exact False.elim (Bool.noConfusion (ht0.symm.trans ht1))
  · intro h0 _ _
    exact Or.inl h0

theorem edge_no_uniform_witness :
    ¬ hasWitness (mustIncidence Set.univ edgeR) edgeC := by
  rintro ⟨t, ht⟩
  have heq : (1 : Fin 3) = 0 :=
    (edge_mustIncidence 1 t).mp (ht 1 (Or.inr rfl))
  exact (by decide : (1 : Fin 3) ≠ 0) heq

theorem edge_no_uniform_conjunction :
    ¬ UniformConjunction Set.univ edgeR (fun _ => edgeC) := by
  intro h
  have hu : uniformColumns Set.univ edgeR (fun _ => edgeC) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    apply edge_no_uniform_witness
    exact ⟨t, fun x hx ω hω => ht ω hω x hx⟩
  have heq := (uniformConjunction_iff Set.univ edgeR (fun _ => edgeC)).mp h
    false (Set.mem_univ _)
  have ht : (2 : Fin 3) ∈ uniformHull Set.univ edgeR (fun _ => edgeC) false := by
    intro t ht
    rw [hu] at ht
    exact False.elim ht
  rw [heq] at ht
  rcases ht with h0 | h1
  · exact (by decide : (2 : Fin 3) ≠ 0) h0
  · exact (by decide : (2 : Fin 3) ≠ 1) h1

/-- Exact conjunction of the correlated counterexample's claims. -/
theorem correlated_edge_counterexample :
    Conservative Set.univ edgeR (fun _ => edgeC) ∧
    (∀ ω, {h | edgeR ω h false ∨ edgeR ω h true} = edgeC) ∧
    (∀ ω, hasWitness (edgeR ω) edgeC) ∧
    ¬ hasWitness (mustIncidence Set.univ edgeR) edgeC ∧
    ¬ UniformConjunction Set.univ edgeR (fun _ => edgeC) :=
  ⟨edge_conservative, edge_disjunction, edge_witness,
    edge_no_uniform_witness, edge_no_uniform_conjunction⟩

end Counterexample

#print axioms closurePreserved_iff
#print axioms nervePreserved_iff
#print axioms conservative_iff_finite
#print axioms conservative_restrict
#print axioms conservative_empty
#print axioms conservative_at_actual
#print axioms closed_extent_cannot_split_rows
#print axioms closurePreserved_futureEquivalent
#print axioms subset_guaranteedClosure
#print axioms guaranteedClosure_mono
#print axioms guaranteedClosure_idempotent
#print axioms guaranteedClosure_restrict
#print axioms subset_closureStep
#print axioms closureStep_mono
#print axioms closureStep_fixed_iff
#print axioms saturation_mono
#print axioms saturation_le_closed
#print axioms saturation_stabilizes
#print axioms commonClosedHull_closed
#print axioms commonClosedHull_least
#print axioms commonClosedHull_fixed_iff
#print axioms commonClosedHull_mono
#print axioms commonClosedHull_idempotent
#print axioms commonClosedHull_restrict
#print axioms uniformConjunction_iff
#print axioms uniformConjunction_closurePreserved
#print axioms mustIncidence_witness_iff
#print axioms mustIncidence_witness_sound
#print axioms Counterexample.switch_closed
#print axioms Counterexample.switch_witness
#print axioms Counterexample.switch_conservative
#print axioms Counterexample.switch_no_uniform_witness
#print axioms Counterexample.robust_nerve_strictly_exceeds_must
#print axioms Counterexample.switch_uniformColumns_empty
#print axioms Counterexample.switch_no_uniform_conjunction
#print axioms Counterexample.guaranteed_closed_not_worldwise
#print axioms Counterexample.mixed_commonClosedHull_univ
#print axioms Counterexample.edge_witness
#print axioms Counterexample.edge_closed
#print axioms Counterexample.edge_disjunction
#print axioms Counterexample.edge_conservative
#print axioms Counterexample.edge_mustIncidence
#print axioms Counterexample.edge_no_uniform_witness
#print axioms Counterexample.edge_no_uniform_conjunction
#print axioms Counterexample.correlated_edge_counterexample

end EvidenceConservativity
