module

public import ContextualComposition.PureSquareCalculus
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-! Reader transposition on a cartesian category when the fixed environment
is exponentiable. Both horizontal operations use the same environment twice. -/

@[expose] public section
namespace ContextualComposition.CartesianReader

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (E : C) {A B D : C}

def withEnvironment : PureSquareCalculus C where
  Hom A B := E ⊗ A ⟶ B
  pure u := snd _ _ ≫ u
  comp f g := lift (fst _ _) f ≫ g
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp [comp_lift_assoc]
  pure_comp _ _ := by simp

variable [Closed E]

abbrev transpose (A B : C) : (E ⊗ A ⟶ B) ≃ (A ⟶ (ihom E).obj B) :=
  (ihom.adjunction E).homEquiv A B

/-- Evaluate the outer reader at e and then evaluate its returned reader at e. -/
def join (B : C) : (ihom E).obj ((ihom E).obj B) ⟶ (ihom E).obj B :=
  curry (lift (fst _ _) ((ihom.ev E).app _) ≫ (ihom.ev E).app B)

def readerPure (u : A ⟶ B) : A ⟶ (ihom E).obj B :=
  u ≫ curry (snd E B)

def readerComp (f : A ⟶ (ihom E).obj B) (g : B ⟶ (ihom E).obj D) : A ⟶ (ihom E).obj D :=
  f ≫ (ihom E).map g ≫ join E D

theorem transpose_pure (u : A ⟶ B) : transpose E A B (snd E A ≫ u) = readerPure E u := by
  change curry _ = u ≫ curry _
  rw [← curry_natural_left]
  simp

theorem uncurry_comp (f : A ⟶ (ihom E).obj B) (g : B ⟶ (ihom E).obj D) :
    uncurry (readerComp E f g) = lift (fst E A) (uncurry f) ≫ uncurry g := by
  simp only [readerComp, join, uncurry_natural_left, uncurry_curry, comp_lift_assoc, whiskerLeft_fst]
  rw [uncurry_eq g, lift_whiskerLeft_assoc]
  rw [← uncurry_eq ((ihom E).map g), uncurry_ihom_map, ← Category.assoc, ← uncurry_eq f]

theorem transpose_comp (f : E ⊗ A ⟶ B) (g : E ⊗ B ⟶ D) :
    transpose E _ _ (lift (fst _ _) f ≫ g) = readerComp E (transpose E _ _ f) (transpose E _ _ g) := by
  apply uncurry_injective
  change uncurry (curry _) = uncurry (readerComp E (curry f) (curry g))
  simp [uncurry_comp]

def reader : PureSquareCalculus C :=
  (withEnvironment E).ofComparison (fun A B => A ⟶ (ihom E).obj B) (transpose E)
    (readerPure E) (readerComp E) (transpose_pure E) (transpose_comp E)

/-- Homwise currying is a strict pure-square double isomorphism. -/
def transposition : (withEnvironment E).Iso (reader E) :=
  ⟨transpose E, transpose_pure E, transpose_comp E⟩

omit [Closed E] in
theorem co_square {A' B' : C} (f : E ⊗ A ⟶ B) (g : E ⊗ A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B') :
    (withEnvironment E).Square f g u v ↔ (E ◁ u) ≫ g = f ≫ v := by
  change (lift (fst _ _) (snd _ _ ≫ u) ≫ g = lift (fst _ _) f ≫ snd _ _ ≫ v) ↔ _
  rw [← lift_whiskerLeft (fst E A) (snd E A) u]
  simp

theorem reader_square {A' B' : C} (f : A ⟶ (ihom E).obj B) (g : A' ⟶ (ihom E).obj B')
    (u : A ⟶ A') (v : B ⟶ B') : (reader E).Square f g u v ↔ u ≫ g = f ≫ (ihom E).map v := by
  have h := (transposition E).square_iff (uncurry f) (uncurry g) u v
  change _ ↔ (reader E).Square (curry (uncurry f)) (curry (uncurry g)) u v at h
  rw [curry_uncurry, curry_uncurry] at h
  rw [← h, co_square, ← uncurry_natural_left, ← uncurry_natural_right]
  exact uncurry_injective.eq_iff

end ContextualComposition.CartesianReader
