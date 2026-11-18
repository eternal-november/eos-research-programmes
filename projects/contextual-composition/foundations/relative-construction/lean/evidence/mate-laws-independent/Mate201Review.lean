import ContextualComposition.MateLaws
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
namespace Independent201
inductive Pt | star
instance : Category Pt where
  Hom _ _ := Int
  id _ := 0
  comp f g := f + g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
def edge (k : Int) (x : Pt) : x ≅ x where
  hom := k
  inv := -k
  hom_inv_id := Int.add_right_neg k
  inv_hom_id := Int.add_left_neg k
def shift (k : Int) : 𝟭 Pt ≅ 𝟭 Pt :=
  NatIso.ofComponents (edge k) (by intro x y f; exact Int.add_comm f k)
def twist (k : Int) : Pt ≌ Pt where
  functor := 𝟭 Pt
  inverse := 𝟭 Pt
  unitIso := shift k
  counitIso := shift (-k)
  functor_unitIso_comp := by intro x; exact Int.add_right_neg k
def cell : (twist 2).functor ⋙ 𝟭 _ ≅ 𝟭 _ ⋙ (twist 8).functor := shift 1
def m := SumChange.inverseSquare (twist 2) (twist 8) cell
example : cell.hom.app Pt.star = (1:Int) := rfl
example : cell.inv.app Pt.star = (-1:Int) := rfl
example : m.hom.app Pt.star = (5:Int) := rfl
example : m.inv.app Pt.star = (-5:Int) := rfl
def cellG (s t h : Int) : (twist s).functor ⋙ 𝟭 Pt ≅ 𝟭 Pt ⋙ (twist t).functor := shift h
example : (SumChange.inverseSquare (twist 8) (twist 20) (cellG 8 20 4)).hom.app Pt.star = (8:Int) := rfl
example : (SumChange.inverseSquare (twist 2) (twist 20) (cellG 2 20 5)).hom.app Pt.star = (13:Int) := rfl
example : FibreValue.Paste.CompLaw
    (SumChange.inverseSquare (twist 2) (twist 20) (cellG 2 20 5)).symm
    (SumChange.inverseSquare (twist 8) (twist 20) (cellG 8 20 4)).symm
    (SumChange.inverseSquare (twist 2) (twist 8) (cellG 2 8 1)).symm
    (𝟙 (𝟭 Pt)) (𝟙 (𝟭 Pt)) :=
  MateLaws.comp (twist 20) (twist 8) (twist 2) _ _ _ _ _ (fun _ => rfl)
open Families MateLaws.All
def Z : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
def z : ZeroPower.weighted presheaf Bool := pair _ _ ⟨Bool,rfl⟩ Z
noncomputable def wholeZ := (presentation splitEndpoints presheaf Bool).functor.obj ⟨0,z⟩
#check evaluationUnit splitEndpoints presheaf Bool wholeZ
#check evaluationComp splitEndpoints presheaf collapse (selectPoint true) wholeZ
example : (ZeroPower.eval presheaf Bool).obj z true = Bool := rfl
example : (ZeroPower.eval presheaf Bool).obj z false = Empty := rfl
example : collapse ≫ selectPoint true ≠ 𝟙 Bool := by
  intro h
  have e := congrArg (fun k : Bool ⟶ Bool => k false) h
  exact Bool.noConfusion e
example : ¬ ∃ s : Bool ⟶ Bool, s ≫ (collapse ≫ selectPoint true) = 𝟙 Bool := by
  rintro ⟨s,h⟩
  exact Bool.noConfusion (congrArg (fun k : Bool ⟶ Bool => k false) h)
end Independent201
