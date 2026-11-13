import Mathlib.Data.Set.Image

/-!
# Exact incidence and closure transport

This file checks a core of the accompanying finite FCA--Dowker note for
arbitrary carrier types (no finiteness or inhabitedness hypotheses).
It does not formalize geometric realization or homotopy equivalence.
-/

namespace CommonIncidenceBridge

universe u v w x y z

def intent {H : Type u} {E : Type v} (R : H → E → Prop) (A : Set H) : Set E :=
  {e | ∀ h, h ∈ A → R h e}

def extent {H : Type u} {E : Type v} (R : H → E → Prop) (B : Set E) : Set H :=
  {h | ∀ e, e ∈ B → R h e}

def closure {H : Type u} {E : Type v} (R : H → E → Prop) (A : Set H) : Set H :=
  extent R (intent R A)

def Chu {H : Type u} {E : Type v} {K : Type w} {D : Type x}
    (R : H → E → Prop) (S : K → D → Prop) (f : H → K) (g : D → E) : Prop :=
  ∀ h d, S (f h) d ↔ R h (g d)

variable {H : Type u} {E : Type v} {K : Type w} {D : Type x}
variable {J : Type y} {F : Type z}
variable {R : H → E → Prop} {S : K → D → Prop} {T : J → F → Prop}
variable {f : H → K} {g : D → E} {p : K → J} {q : F → D}

theorem subset_closure (A : Set H) : A ⊆ closure R A := by
  intro h ha e he
  exact he h ha

theorem intent_closure (A : Set H) : intent R (closure R A) = intent R A := by
  ext e
  constructor
  · intro hc h ha
    exact hc h (subset_closure A ha)
  · intro hi h hc
    exact hc e hi

theorem image_intent (adj : Chu R S f g) (A : Set H) :
    intent S (f '' A) = g ⁻¹' intent R A := by
  ext d
  constructor
  · intro hi h ha
    exact (adj h d).mp (hi (f h) ⟨h, ha, rfl⟩)
  · intro hi k hk
    obtain ⟨h, ha, rfl⟩ := hk
    exact (adj h d).mpr (hi h ha)

theorem image_intent_closure (adj : Chu R S f g) (A : Set H) :
    intent S (f '' closure R A) = intent S (f '' A) := by
  simp only [image_intent adj, intent_closure]

theorem closure_image_closure (adj : Chu R S f g) (A : Set H) :
    closure S (f '' closure R A) = closure S (f '' A) := by
  change extent S (intent S (f '' closure R A)) = extent S (intent S (f '' A))
  rw [image_intent_closure adj A]

theorem chu_comp (adj₁ : Chu R S f g) (adj₂ : Chu S T p q) :
    Chu R T (p ∘ f) (g ∘ q) := by
  intro h e
  exact (adj₂ (f h) e).trans (adj₁ h (q e))

theorem closure_lift_comp (adj₂ : Chu S T p q) (A : Set H) :
    closure T (p '' closure S (f '' A)) = closure T ((p ∘ f) '' A) := by
  rw [closure_image_closure adj₂]
  simp only [Set.image_image, Function.comp_def]

theorem image_witness_pullback (adj : Chu R S f g) {A : Set H}
    (hw : (intent S (f '' A)).Nonempty) : (intent R A).Nonempty := by
  obtain ⟨d, hd⟩ := hw
  refine ⟨g d, ?_⟩
  intro h ha
  exact (adj h d).mp (hd (f h) ⟨h, ha, rfl⟩)

theorem image_witness_iff (adj : Chu R S f g) (A : Set H) :
    (intent S (f '' A)).Nonempty ↔ (intent R A ∩ Set.range g).Nonempty := by
  rw [image_intent adj A]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨g d, hd, ⟨d, rfl⟩⟩
  · rintro ⟨e, he, d, rfl⟩
    exact ⟨d, he⟩

theorem partial_domain_comp (adj₂ : Chu S T p q) (A : Set H) :
    (A.Nonempty ∧ (intent T ((p ∘ f) '' A)).Nonempty) ↔
      (A.Nonempty ∧ (intent S (f '' A)).Nonempty) ∧
      ((f '' A).Nonempty ∧ (intent T (p '' (f '' A))).Nonempty) := by
  constructor
  · rintro ⟨ha, ht⟩
    have ht' : (intent T (p '' (f '' A))).Nonempty := by
      simpa only [Set.image_image, Function.comp_def] using ht
    have hs : (intent S (f '' A)).Nonempty := image_witness_pullback adj₂ ht'
    have hfa : (f '' A).Nonempty := by
      obtain ⟨a, ha⟩ := ha
      exact ⟨f a, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨ha, hs⟩, ⟨hfa, ht'⟩⟩
  · rintro ⟨⟨ha, _⟩, ⟨_, ht⟩⟩
    exact ⟨ha, by simpa only [Set.image_image, Function.comp_def] using ht⟩

theorem closure_preserves_witness_domain (adj : Chu R S f g) (A : Set H) :
    (intent S (f '' closure R A)).Nonempty ↔
      (intent S (f '' A)).Nonempty := by
  rw [image_intent_closure adj A]

#print axioms image_intent
#print axioms closure_image_closure
#print axioms closure_lift_comp
#print axioms partial_domain_comp

end CommonIncidenceBridge
