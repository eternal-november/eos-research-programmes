import Mathlib

namespace EvolvingTests
variable {X Y : Type} (old new : Set (Set X))

def ObsEq (E : Set (Set X)) (x y : X) : Prop := ∀ S ∈ E, (x ∈ S ↔ y ∈ S)

def obsSetoid (E : Set (Set X)) : Setoid X where
  r := ObsEq E
  iseqv := ⟨by intro x S hS; rfl,
    by intro x y h S hS; exact (h S hS).symm,
    by intro x y z hxy hyz S hS; exact (hxy S hS).trans (hyz S hS)⟩

def forget (h : old ⊆ new) : Quotient (obsSetoid new) → Quotient (obsSetoid old) :=
  Quotient.map id (by intro x y hxy S hS; exact hxy S (h hS))

theorem forget_surjective (h : old ⊆ new) : Function.Surjective (forget old new h) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk (obsSetoid new) x, rfl⟩

def Stable (E : Set (Set X)) (f : X → X) : Prop := ∀ S ∈ E, f ⁻¹' S ∈ E

def induced (E : Set (Set X)) (f : X → X) (hf : Stable E f) : Quotient (obsSetoid E) → Quotient (obsSetoid E) :=
  Quotient.map f (by intro x y hxy S hS; exact hxy (f ⁻¹' S) (hf S hS))

theorem refinement_natural (h : old ⊆ new) (f : X → X)
    (ho : Stable old f) (hn : Stable new f) :
    forget old new h ∘ induced new f hn = induced old f ho ∘ forget old new h := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

theorem exact_obstruction (h : old ⊆ new) (x y : X)
    (hxy : ObsEq old x y) (S : Set X) (hS : S ∈ new) (hd : ¬ (x ∈ S ↔ y ∈ S)) :
    forget old new h (Quotient.mk (obsSetoid new) x) =
      forget old new h (Quotient.mk (obsSetoid new) y) ∧
    Quotient.mk (obsSetoid new) x ≠ Quotient.mk (obsSetoid new) y := by
  constructor
  · exact Quotient.sound hxy
  · intro heq
    have hrel : ObsEq new x y := Quotient.exact heq
    exact hd (hrel S hS)

#print axioms forget_surjective
#print axioms refinement_natural
#print axioms exact_obstruction
end EvolvingTests
