module

public import Mathlib.CategoryTheory.Monad.Kleisli

@[expose] public section

/-! Fixed-effect recovery with pure changing-endpoint squares.
Source: Relative construction, §Internal constructors and familiar specializations.
This file does not claim the category-valued relative pseudocoend construction. -/
namespace ContextualComposition
open CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]

namespace MonadRecovery
variable (T : Monad C)
abbrev Arrow (A B : C) := A ⟶ T.obj B
abbrev comp {A B D : C} (f : Arrow T A B) (g : Arrow T B D) : Arrow T A D :=
  f ≫ T.map g ≫ T.μ.app D
abbrev pure {A B : C} (f : A ⟶ B) : Arrow T A B := f ≫ T.η.app B

def Square {A B A' B' : C} (f : Arrow T A B) (g : Arrow T A' B')
    (a : A ⟶ A') (b : B ⟶ B') : Prop := f ≫ T.map b = a ≫ g

theorem square_iff_quintet {A B A' B' : C} (f : Arrow T A B)
    (g : Arrow T A' B') (a : A ⟶ A') (b : B ⟶ B') :
    Square T f g a b ↔ comp T f (pure T b) = comp T (pure T a) g := by
  simp only [Square, comp, pure, Functor.map_comp, Category.assoc]
  simp only [Monad.right_unit, ← T.η.naturality_assoc g]
  simp

theorem horizontal {A B D A' B' D' : C}
    {f : Arrow T A B} {g : Arrow T B D} {f' : Arrow T A' B'} {g' : Arrow T B' D'}
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'}
    (hf : Square T f f' a b) (hg : Square T g g' b d) :
    Square T (comp T f g) (comp T f' g') a d := by
  dsimp [Square, comp] at *
  rw [Category.assoc, Category.assoc, ← T.μ.naturality]
  simp only [Functor.comp_map]
  rw [← Category.assoc (T.map g), ← Functor.map_comp, hg, Functor.map_comp]
  simp only [← Category.assoc]
  rw [hf]

theorem vertical {A B A' B' A'' B'' : C}
    {f : Arrow T A B} {g : Arrow T A' B'} {h : Arrow T A'' B''}
    {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}
    (hf : Square T f g a b) (hg : Square T g h a' b') :
    Square T f h (a ≫ a') (b ≫ b') := by
  dsimp [Square] at *
  rw [Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg, Category.assoc]

/-- Literal operational recovery, not a quotient of native cells. -/
theorem kleisli_comp {A B D : C} (f : Arrow T A B) (g : Arrow T B D) :
    comp T f g = Kleisli.Hom.of (@CategoryStruct.comp (Kleisli T) (Kleisli.category T).toCategoryStruct
      (Kleisli.mk T A) (Kleisli.mk T B) (Kleisli.mk T D) ⟨f⟩ ⟨g⟩) := rfl
end MonadRecovery

namespace ComonadRecovery
variable (G : Comonad C)
abbrev Arrow (A B : C) := G.obj A ⟶ B
abbrev comp {A B D : C} (f : Arrow G A B) (g : Arrow G B D) : Arrow G A D :=
  G.δ.app A ≫ G.map f ≫ g
abbrev pure {A B : C} (f : A ⟶ B) : Arrow G A B := G.ε.app A ≫ f

def Square {A B A' B' : C} (f : Arrow G A B) (g : Arrow G A' B')
    (a : A ⟶ A') (b : B ⟶ B') : Prop := f ≫ b = G.map a ≫ g

theorem square_iff_quintet {A B A' B' : C} (f : Arrow G A B)
    (g : Arrow G A' B') (a : A ⟶ A') (b : B ⟶ B') :
    Square G f g a b ↔ comp G f (pure G b) = comp G (pure G a) g := by
  simp [Square, comp, pure, ← Category.assoc]

theorem horizontal {A B D A' B' D' : C}
    {f : Arrow G A B} {g : Arrow G B D} {f' : Arrow G A' B'} {g' : Arrow G B' D'}
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'}
    (hf : Square G f f' a b) (hg : Square G g g' b d) :
    Square G (comp G f g) (comp G f' g') a d := by
  dsimp [Square, comp] at *
  simp only [Category.assoc]
  rw [hg, ← Category.assoc (G.map f), ← Functor.map_comp, hf, Functor.map_comp]
  simp only [← Category.assoc]
  have hn : G.map a ≫ G.δ.app A' = G.δ.app A ≫ G.map (G.map a) := G.δ.naturality a
  rw [← hn]

theorem vertical {A B A' B' A'' B'' : C}
    {f : Arrow G A B} {g : Arrow G A' B'} {h : Arrow G A'' B''}
    {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}
    (hf : Square G f g a b) (hg : Square G g h a' b') :
    Square G f h (a ≫ a') (b ≫ b') := by
  dsimp [Square] at *
  rw [← Category.assoc, hf, Category.assoc, hg, Functor.map_comp, Category.assoc]

theorem cokleisli_comp {A B D : C} (f : Arrow G A B) (g : Arrow G B D) :
    comp G f g = Cokleisli.Hom.of (@CategoryStruct.comp (Cokleisli G) (Cokleisli.category G).toCategoryStruct
      (Cokleisli.mk G A) (Cokleisli.mk G B) (Cokleisli.mk G D) ⟨f⟩ ⟨g⟩) := rfl
end ComonadRecovery
end ContextualComposition
