module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
Toolchain smoke checks only. This is not an implementation of the proposed
witnessed-decomposition multicategory or its semantics.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe v u

namespace WitnessedDecompositions.Smoke

section Category
variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

/-- Check that mathlib's category composition and simplifier are ready. -/
theorem identity_and_associativity (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (𝟙 W ≫ f) ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  simp only [Category.id_comp, Category.assoc]
end Category

section Paths
variable {V : Type u} [Quiver.{v} V]
variable {a b c : V}

/-- Check endpoint-indexed quiver paths and their concrete composition. -/
theorem path_length_composition (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (p.comp q).length = p.length + q.length := by
  simp

/-- Check the free path-category instance. -/
example (X Y : Paths V) (p : X ⟶ Y) : 𝟙 X ≫ p = p := by
  simp
end Paths

section Monoidal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Check availability of monoidal structure without assuming any new theorem. -/
example (X Y Z : C) : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  MonoidalCategory.associator X Y Z
end Monoidal

end WitnessedDecompositions.Smoke
