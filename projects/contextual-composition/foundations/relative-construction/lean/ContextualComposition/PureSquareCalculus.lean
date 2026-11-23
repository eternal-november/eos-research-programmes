module

public import Mathlib.CategoryTheory.Category.Basic

/-! A strict horizontal category on the objects of a base category, with its
identity-on-objects pure functor. Its double-category squares are the
commuting squares with pure vertical sides. -/

@[expose] public section

namespace ContextualComposition
open CategoryTheory

universe v u w w'

structure PureSquareCalculus (C : Type u) [Category.{v} C] where
  Hom : C → C → Type w
  pure : ∀ {A B}, (A ⟶ B) → Hom A B
  comp : ∀ {A B D}, Hom A B → Hom B D → Hom A D
  id_comp : ∀ {A B} (f : Hom A B), comp (pure (𝟙 A)) f = f
  comp_id : ∀ {A B} (f : Hom A B), comp f (pure (𝟙 B)) = f
  assoc : ∀ {A B D E} (f : Hom A B) (g : Hom B D) (h : Hom D E),
    comp (comp f g) h = comp f (comp g h)
  pure_comp : ∀ {A B D} (f : A ⟶ B) (g : B ⟶ D), comp (pure f) (pure g) = pure (f ≫ g)

namespace PureSquareCalculus
variable {C : Type u} [Category.{v} C]
variable (P : PureSquareCalculus C)

def Square {A B A' B'} (f : P.Hom A B) (g : P.Hom A' B') (u : A ⟶ A') (v : B ⟶ B') : Prop :=
  P.comp (P.pure u) g = P.comp f (P.pure v)

theorem vertical_identity {A B} (f : P.Hom A B) : P.Square f f (𝟙 A) (𝟙 B) := by
  simp [Square, P.id_comp, P.comp_id]

theorem horizontal_identity {A B} (u : A ⟶ B) : P.Square (P.pure (𝟙 A)) (P.pure (𝟙 B)) u u := by
  simp [Square, P.id_comp, P.comp_id]

theorem vertical {A B A' B' A'' B''} {f : P.Hom A B} {g : P.Hom A' B'} {h : P.Hom A'' B''}
    {u : A ⟶ A'} {v : B ⟶ B'} {u' : A' ⟶ A''} {v' : B' ⟶ B''}
    (s : P.Square f g u v) (t : P.Square g h u' v') : P.Square f h (u ≫ u') (v ≫ v') := by
  unfold Square at *
  rw [← P.pure_comp, P.assoc, t, ← P.assoc, s, P.assoc, P.pure_comp]

theorem horizontal {A B D A' B' D'} {f : P.Hom A B} {f' : P.Hom A' B'} {g : P.Hom B D} {g' : P.Hom B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    (s : P.Square f f' u v) (t : P.Square g g' v w) : P.Square (P.comp f g) (P.comp f' g') u w := by
  unfold Square at *
  rw [← P.assoc, s, P.assoc, t, ← P.assoc]

/-- Supply the operations of the second presentation and their comparisons;
the horizontal category and pure-functor laws then transfer across the
specified hom-bijections. -/
def ofComparison (H : C → C → Type w') (e : ∀ A B, P.Hom A B ≃ H A B)
    (pure : ∀ {A B}, (A ⟶ B) → H A B) (comp : ∀ {A B D}, H A B → H B D → H A D)
    (unit : ∀ {A B} (u : A ⟶ B), e A B (P.pure u) = pure u)
    (mult : ∀ {A B D} (f : P.Hom A B) (g : P.Hom B D), e A D (P.comp f g) = comp (e _ _ f) (e _ _ g)) :
    PureSquareCalculus C where
  Hom := H
  pure := pure
  comp := comp
  id_comp f := by obtain ⟨f,rfl⟩ := (e _ _).surjective f; rw [← unit, ← mult, P.id_comp]
  comp_id f := by obtain ⟨f,rfl⟩ := (e _ _).surjective f; rw [← unit, ← mult, P.comp_id]
  assoc f g h := by
    obtain ⟨f,rfl⟩ := (e _ _).surjective f
    obtain ⟨g,rfl⟩ := (e _ _).surjective g
    obtain ⟨h,rfl⟩ := (e _ _).surjective h
    simp only [← mult, P.assoc]
  pure_comp f g := by rw [← unit, ← unit g, ← mult, P.pure_comp, unit]

/-- The pure-square double isomorphism fixes objects and vertical arrows.
Squares are propositions, hence their parallel pastings are unique. -/
structure Iso (P : PureSquareCalculus.{v,u,w} C) (Q : PureSquareCalculus.{v,u,w'} C) where
  homEquiv : ∀ A B, P.Hom A B ≃ Q.Hom A B
  pure_eq : ∀ {A B} (u : A ⟶ B), homEquiv _ _ (P.pure u) = Q.pure u
  comp_eq : ∀ {A B D} (f : P.Hom A B) (g : P.Hom B D),
    homEquiv _ _ (P.comp f g) = Q.comp (homEquiv _ _ f) (homEquiv _ _ g)

variable {P} {Q : PureSquareCalculus C}

theorem Iso.square_iff (i : Iso P Q) {A B A' B'} (f : P.Hom A B) (g : P.Hom A' B') (u : A ⟶ A') (v : B ⟶ B') :
    P.Square f g u v ↔ Q.Square (i.homEquiv _ _ f) (i.homEquiv _ _ g) u v := by
  unfold Square
  rw [← i.pure_eq u, ← i.pure_eq v, ← i.comp_eq, ← i.comp_eq, Equiv.apply_eq_iff_eq]

def Iso.symm (i : Iso P Q) : Iso Q P where
  homEquiv A B := (i.homEquiv A B).symm
  pure_eq u := (i.homEquiv _ _).symm_apply_eq.mpr (i.pure_eq u).symm
  comp_eq f g := (i.homEquiv _ _).symm_apply_eq.mpr (by simp [i.comp_eq])

theorem Iso.doubleInverse (i : Iso P Q) : i.symm.symm = i := by cases i; rfl

end PureSquareCalculus
end ContextualComposition
