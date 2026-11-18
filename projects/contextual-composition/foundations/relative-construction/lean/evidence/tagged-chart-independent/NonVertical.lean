import ContextualComposition.SuffixCell
import Mathlib.CategoryTheory.Types.Basic
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open SpanApex BoundaryPaste SuffixCell
namespace NonVertical
abbrev D := Discrete Unit
abbrev p := (Functor.const D).obj (Bool : Type)
abbrev q := 𝟭 (Type)
theorem h : p ⋙ q = p := rfl
def a : p ⟶ p where
  app _ := TypeCat.ofHom Bool.not
  naturality _ _ _ := rfl
example : ¬ vertical p q h h a := by
  intro v
  have k := congrArg (fun g : (Bool : Type) ⟶ Bool => g false) (v (Discrete.mk ()))
  exact Bool.noConfusion k
end NonVertical
