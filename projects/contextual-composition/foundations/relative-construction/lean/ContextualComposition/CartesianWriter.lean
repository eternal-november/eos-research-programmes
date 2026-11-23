module

public import ContextualComposition.PureSquareCalculus
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! Writer transposition for an internal monoid in a cartesian category.
The grade is a morphism from the source into the monoid object. -/

@[expose] public section
namespace ContextualComposition.CartesianWriter

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (W : C) [MonObj W] {A B D : C}

abbrev Graded (A B : C) := (A ⟶ W) × (A ⟶ B)

def gradedPure (u : A ⟶ B) : Graded W A B := (1, u)

def gradedComp (f : Graded W A B) (g : Graded W B D) : Graded W A D :=
  (f.1 * (f.2 ≫ g.1), f.2 ≫ g.2)

def graded : PureSquareCalculus C where
  Hom := Graded W
  pure := gradedPure W
  comp := gradedComp W
  id_comp _ := by simp [gradedPure, gradedComp]
  comp_id _ := by simp [gradedPure, gradedComp, MonObj.comp_one]
  assoc _ _ _ := by simp [gradedComp, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  pure_comp _ _ := by simp [gradedPure, gradedComp, MonObj.comp_one]

def writerPure (u : A ⟶ B) : A ⟶ W ⊗ B := lift (toUnit A ≫ η[W]) u

/-- Multiply the first grade by the second grade; no commutativity is assumed. -/
def join (D : C) : W ⊗ (W ⊗ D) ⟶ W ⊗ D := (α_ W W D).inv ≫ (μ[W] ▷ D)

def writerComp (f : A ⟶ W ⊗ B) (g : B ⟶ W ⊗ D) : A ⟶ W ⊗ D :=
  f ≫ (W ◁ g) ≫ join W D

def pack (A B : C) : Graded W A B ≃ (A ⟶ W ⊗ B) := liftEquiv

theorem pack_pure (u : A ⟶ B) : pack W _ _ (gradedPure W u) = writerPure W u := rfl

theorem pack_comp (f : Graded W A B) (g : Graded W B D) :
    pack W _ _ (gradedComp W f g) = writerComp W (pack W _ _ f) (pack W _ _ g) := by
  change lift (f.1 * (f.2 ≫ g.1)) (f.2 ≫ g.2) =
    lift f.1 f.2 ≫ (W ◁ lift g.1 g.2) ≫ (α_ W W D).inv ≫ (μ[W] ▷ D)
  simp [lift_lift_associator_inv_assoc]
  rfl

def writer : PureSquareCalculus C :=
  (graded W).ofComparison (fun A B => A ⟶ W ⊗ B) (pack W)
    (writerPure W) (writerComp W) (pack_pure W) (pack_comp W)

/-- The product pairing is a strict pure-square double isomorphism. -/
def transposition : (graded W).Iso (writer W) :=
  ⟨pack W, pack_pure W, pack_comp W⟩

theorem graded_square {A' B' : C} (f : Graded W A B) (g : Graded W A' B') (u : A ⟶ A') (v : B ⟶ B') :
    (graded W).Square f g u v ↔ u ≫ g.1 = f.1 ∧ u ≫ g.2 = f.2 ≫ v := by
  change gradedComp W (gradedPure W u) g = gradedComp W f (gradedPure W v) ↔ _
  simp [gradedComp, gradedPure, MonObj.comp_one, Prod.mk.injEq]

theorem writer_square {A' B' : C} (f : A ⟶ W ⊗ B) (g : A' ⟶ W ⊗ B') (u : A ⟶ A') (v : B ⟶ B') :
    (writer W).Square f g u v ↔ u ≫ g = f ≫ (W ◁ v) := by
  let p := (pack W A B).symm f
  let q := (pack W A' B').symm g
  have h := (transposition W).square_iff p q u v
  change _ ↔ (writer W).Square (pack W _ _ p) (pack W _ _ q) u v at h
  simp only [p,q,Equiv.apply_symm_apply] at h
  rw [← h, graded_square]
  change (u ≫ g ≫ fst _ _ = f ≫ fst _ _ ∧ u ≫ g ≫ snd _ _ = (f ≫ snd _ _) ≫ v) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa [Category.assoc] using h₁
    · simpa [Category.assoc] using h₂
  · intro eq
    constructor
    · simpa [Category.assoc] using congrArg (fun k => k ≫ fst W B') eq
    · simpa [Category.assoc] using congrArg (fun k => k ≫ snd W B') eq

end ContextualComposition.CartesianWriter
