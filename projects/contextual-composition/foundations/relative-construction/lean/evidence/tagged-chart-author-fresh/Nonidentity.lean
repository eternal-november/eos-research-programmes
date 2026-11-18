import ContextualComposition.SuffixCell
import Mathlib.CategoryTheory.Types.Basic
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open SpanApex BoundaryPaste SuffixCell
namespace Nonidentity
abbrev D := Discrete Unit
abbrev e : D ⥤ D := 𝟭 _
abbrev q := (Functor.const (Type)).obj (Discrete.mk ())
abbrev p := (Functor.const D).obj (Discrete.mk ())
abbrev H := (Functor.const D).obj (Bool : Type)
theorem over : H ⋙ q = p := rfl
def swap : H ⟶ H where
  app _ := TypeCat.ofHom Bool.not
  naturality _ _ _ := by rfl
theorem w : vertical p q over over swap := fun _ => rfl
def x : Strict.Match e p := ⟨⟨()⟩,⟨()⟩,rfl⟩
example : ((Strict.snd e q).map ((alongCell e p q over over swap w).app x)) false = true := rfl
example : (alongCell e p q over over swap w).app x ≠ 𝟙 _ := by
  intro h
  have z := congrArg (fun a : (along e p q H over).obj x ⟶ (along e p q H over).obj x => ((Strict.snd e q).map a) false) h
  exact Bool.noConfusion z
end Nonidentity
