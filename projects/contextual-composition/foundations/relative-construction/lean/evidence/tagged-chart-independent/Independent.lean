import ContextualComposition.SuffixCell
import Mathlib.CategoryTheory.Types.Basic
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open SpanApex BoundaryPaste SuffixCell
namespace Independent
abbrev B := Discrete Unit
abbrev e := (Functor.const (Type)).obj (Discrete.mk ())
abbrev H := 𝟭 (Type)
def x : Strict.Match e e := ⟨Bool,Bool,rfl⟩
def f : x ⟶ x := ⟨⟨TypeCat.ofHom Bool.not, TypeCat.ofHom (fun _ => false),rfl⟩⟩
example : ((along e e e H rfl).map f).hom.fst false = true := rfl
example : ((along e e e H rfl).map f).hom.snd true = false := rfl
abbrev T := (Functor.const (Type)).obj Bool
def a : T ⟶ T where
  app _ := TypeCat.ofHom (fun _ => false)
  naturality _ _ _ := rfl
example : ((alongCell e e e (H:=T) (T:=T) rfl rfl a (fun _ => rfl)).app x).hom.snd true = false := rfl
example : (alongCell e e e (H:=T) (T:=T) rfl rfl a (fun _ => rfl)).app x ≫
    (along e e e T rfl).map f = (along e e e T rfl).map f ≫
    (alongCell e e e (H:=T) (T:=T) rfl rfl a (fun _ => rfl)).app x :=
  ((alongCell e e e (H:=T) (T:=T) rfl rfl a (fun _ => rfl)).naturality f).symm
end Independent
