import Mathlib.Data.Set.Finite.Basic

/-!
# Adding generated attributes to an incidence relation

All carriers may be empty or infinite. No theorem assumes inhabitedness.
An `Option T` attribute is an old attribute (`some t`) or the new attribute
(`none`), whose extent is the prescribed set `C`.

The closure theorem concerns literal equality of closure operators on the
same object set, not merely an abstract isomorphism of concept lattices.
The nerve theorem uses finite **nonempty** faces; its only finiteness
assumption is that the newly added column `C` is finite.

This file does not formalize topological realization or homotopy equivalence.
-/

namespace GeneratedTests

universe u v w

variable {H : Type u} {T : Type v}

/-- The FCA extent closure obtained by intersecting all old columns containing A. -/
def closure (R : H → T → Prop) (A : Set H) : Set H :=
  {h | ∀ t, (∀ x, x ∈ A → R x t) → R h t}

/-- Add one attribute with precisely the prescribed extent C. -/
def addAttribute (R : H → T → Prop) (C : Set H) : H → Option T → Prop
  | h, none => h ∈ C
  | h, some t => R h t

theorem subset_closure (R : H → T → Prop) (A : Set H) :
    A ⊆ closure R A := by
  intro h ha t ht
  exact ht h ha

theorem closure_mono (R : H → T → Prop) {A B : Set H} (hab : A ⊆ B) :
    closure R A ⊆ closure R B := by
  intro h hh t ht
  exact hh t (fun x hx => ht x (hab hx))

theorem closure_idempotent (R : H → T → Prop) (A : Set H) :
    closure R (closure R A) = closure R A := by
  apply Set.Subset.antisymm
  · intro h hh t ht
    exact hh t (fun x hx => hx t ht)
  · exact subset_closure R (closure R A)

/-- Exact effect of adding the column: it cuts the old closure only if A lies in C. -/
theorem mem_closure_addAttribute_iff (R : H → T → Prop) (C A : Set H) (h : H) :
    h ∈ closure (addAttribute R C) A ↔
      h ∈ closure R A ∧ (A ⊆ C → h ∈ C) := by
  constructor
  · intro hh
    constructor
    · intro t ht
      exact hh (some t) ht
    · intro hac
      exact hh none (fun _ hx => hac hx)
  · rintro ⟨hh, hc⟩ t ht
    cases t with
    | none => exact hc (fun _ hx => ht _ hx)
    | some t => exact hh t ht

/-- The added column itself is closed in the extended context, including C = ∅. -/
theorem added_column_closed (R : H → T → Prop) (C : Set H) :
    closure (addAttribute R C) C = C := by
  apply Set.Subset.antisymm
  · intro h hh
    exact hh none (fun _ hx => hx)
  · exact subset_closure (addAttribute R C) C

/-- Adding C preserves the closure of every subset iff C was already closed. -/
theorem addAttribute_preserves_closure_iff (R : H → T → Prop) (C : Set H) :
    (∀ A : Set H, closure (addAttribute R C) A = closure R A) ↔
      closure R C = C := by
  constructor
  · intro heq
    exact (heq C).symm.trans (added_column_closed R C)
  · intro hc A
    ext h
    rw [mem_closure_addAttribute_iff]
    constructor
    · exact And.left
    · intro hh
      refine ⟨hh, ?_⟩
      intro hac
      have hhc : h ∈ closure R C := closure_mono R hac hh
      rwa [hc] at hhc

/-- The same result as literal function equality of the two closure operators. -/
theorem addAttribute_closure_operator_eq_iff (R : H → T → Prop) (C : Set H) :
    closure (addAttribute R C) = closure R ↔ closure R C = C := by
  constructor
  · intro heq
    exact (addAttribute_preserves_closure_iff R C).mp (congrFun heq)
  · intro hc
    exact funext ((addAttribute_preserves_closure_iff R C).mpr hc)

/-- The complete observable row of an object. -/
def rowProfile (R : H → T → Prop) (h : H) : Set T := {t | R h t}

/-- Any pointwise test computed solely from the original row is row-invariant. -/
theorem pointwise_test_cannot_split_rows (R : H → T → Prop)
    (F : Set T → Prop) {h k : H} (hrows : ∀ t, R h t ↔ R k t) :
    F (rowProfile R h) ↔ F (rowProfile R k) := by
  have heq : rowProfile R h = rowProfile R k := Set.ext hrows
  rw [heq]

/-- Even an arbitrary family of pointwise-derived attributes cannot split rows. -/
theorem pointwise_family_cannot_split_rows {J : Type w}
    (R : H → T → Prop) (F : J → Set T → Prop)
    {h k : H} (hrows : ∀ t, R h t ↔ R k t) :
    ∀ j, F j (rowProfile R h) ↔ F j (rowProfile R k) := by
  intro j
  exact pointwise_test_cannot_split_rows R (F j) hrows

/-- A common attribute witnesses A as a face on the object side. -/
def hasWitness (R : H → T → Prop) (A : Set H) : Prop :=
  ∃ t, ∀ h, h ∈ A → R h t

theorem hasWitness_addAttribute_iff (R : H → T → Prop) (C A : Set H) :
    hasWitness (addAttribute R C) A ↔ hasWitness R A ∨ A ⊆ C := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | none => exact Or.inr (fun _ hx => ht _ hx)
    | some t => exact Or.inl ⟨t, ht⟩
  · rintro (⟨t, ht⟩ | hac)
    · exact ⟨some t, ht⟩
    · exact ⟨none, fun _ hx => hac hx⟩

/--
For a finite new column, finite nonempty object-side nerve faces are unchanged
iff, whenever C is nonempty, one old column contains all of C.
If C is empty the criterion is vacuous, even if there are no old attributes.
-/
theorem finite_nonempty_nerve_unchanged_iff
    (R : H → T → Prop) (C : Set H) (hC : C.Finite) :
    (∀ A : Set H, A.Finite → A.Nonempty →
      (hasWitness (addAttribute R C) A ↔ hasWitness R A)) ↔
    (C.Nonempty → hasWitness R C) := by
  constructor
  · intro hsame hne
    apply (hsame C hC hne).mp
    exact ⟨none, fun _ hx => hx⟩
  · intro hc A _ hne
    rw [hasWitness_addAttribute_iff]
    constructor
    · rintro (hw | hac)
      · exact hw
      · have hcn : C.Nonempty := by
          obtain ⟨h, hh⟩ := hne
          exact ⟨h, hac hh⟩
        obtain ⟨t, ht⟩ := hc hcn
        exact ⟨t, fun h hh => ht h (hac hh)⟩
    · exact Or.inl

#print axioms subset_closure
#print axioms closure_mono
#print axioms closure_idempotent
#print axioms mem_closure_addAttribute_iff
#print axioms added_column_closed
#print axioms addAttribute_preserves_closure_iff
#print axioms addAttribute_closure_operator_eq_iff
#print axioms pointwise_test_cannot_split_rows
#print axioms pointwise_family_cannot_split_rows
#print axioms hasWitness_addAttribute_iff
#print axioms finite_nonempty_nerve_unchanged_iff

end GeneratedTests
