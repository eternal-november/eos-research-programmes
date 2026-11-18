import ContextualComposition.SuffixCell
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Products.Basic
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open SpanApex BoundaryPaste SuffixCell
namespace MovingBase
abbrev e := 𝟭 (Type)
abbrev q := CategoryTheory.Prod.fst (Type) (Type)
abbrev T := (Functor.const (Type)).obj Bool
abbrev H := e.prod' T
theorem h : H ⋙ q = e := rfl
def a : T ⟶ T where
  app _ := TypeCat.ofHom (fun _ => false)
  naturality _ _ _ := rfl
abbrev v := NatTrans.prod' (𝟙 e) a
theorem over : vertical e q h h v := fun _ => rfl
def x : Strict.Match e e := ⟨Bool,Bool,rfl⟩
def f : x ⟶ x := ⟨⟨TypeCat.ofHom Bool.not,TypeCat.ofHom Bool.not,by rfl⟩⟩
abbrev A := alongCell e e q h h v over
example : ((along e e q H h).map f).hom.fst false = true := rfl
example : ((along e e q H h).map f).hom.snd.1 false = true := rfl
example : (A.app x).hom.snd.2 true = false := rfl
example : ((along e e q H h).map f ≫ A.app x).hom.snd.1 false = true := rfl
example : ((along e e q H h).map f ≫ A.app x).hom.snd.2 true = false := rfl
example : (along e e q H h).map f ≫ A.app x = A.app x ≫ (along e e q H h).map f := A.naturality f
end MovingBase
