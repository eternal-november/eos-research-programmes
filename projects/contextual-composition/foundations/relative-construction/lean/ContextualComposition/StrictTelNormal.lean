module
public import ContextualComposition.StrictTelAlgebra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelNormal
open CategoryTheory NativeCleavage SpanApex NativeBlocks
open StrictSpanAlgebra
universe b w
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{max b w} B] {U : Span (B := B)}
variable (p : U.apex ⥤ B) (c : Cleavage p)

/-- Optional normalization changes exactly the identity lifts. No
composition equation for the cleavage is imposed. -/
noncomputable def normalize : Cleavage p := fun A y a => by
  classical
  by_cases e : A = p.obj y
  · by_cases h : eqToHom e.symm ≫ a = 𝟙 (p.obj y)
    · exact ⟨y,e.symm,𝟙 y,by rw [Functor.map_id,h],Route.cartId p y⟩
    · exact c A y a
  · exact c A y a

theorem normal : Normal p (normalize p c) := by
  intro y
  classical
  have hh : normalize p c (p.obj y) y (𝟙 (p.obj y)) =
      ⟨y,rfl,𝟙 y,by simp,Route.cartId p y⟩ := by
    unfold normalize
    split
    · rename_i e
      have h : eqToHom e.symm ≫ 𝟙 (p.obj y) = 𝟙 (p.obj y) := by simp
      rw [dite_eq_left h]
    · contradiction
  rw [hh]
  exact ⟨rfl,HEq.rfl⟩

theorem unchangedDifferent (A : B) (y : U.apex) (a : A ⟶ p.obj y) (h : A ≠ p.obj y) :
    normalize p c A y a = c A y a := by
  classical
  simp [normalize,h]

theorem unchangedNonidentity (A : B) (y : U.apex) (a : A ⟶ p.obj y)
    (h : ¬ HEq a (𝟙 (p.obj y))) : normalize p c A y a = c A y a := by
  classical
  by_cases e : A = p.obj y
  · subst A
    have q₀ : a ≠ 𝟙 (p.obj y) := fun e => h (heq_of_eq e)
    simp [normalize,q₀]
  · exact unchangedDifferent p c A y a e
end ContextualComposition.GrothendieckStep.StrictTelNormal
