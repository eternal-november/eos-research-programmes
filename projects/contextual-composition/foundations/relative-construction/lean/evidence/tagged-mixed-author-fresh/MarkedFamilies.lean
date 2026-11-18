import ContextualComposition.TaggedMixed
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace TaggedMixedProbe
/-- Add a Boolean marker to every element, independently at every index. -/
def doubled (A : Type) : presheaf.obj (op A) ⥤ presheaf.obj (op A) where
  obj X := fun b => Bool × X b
  map f := fun b => TypeCat.ofHom (fun p => (p.1, (f b).hom p.2))
  map_id _ := rfl
  map_comp _ _ := rfl
def twice : presheaf ⟶ presheaf where
  app A := (doubled A.unop).toCatHom
  naturality _ _ _ := rfl

/-- A marker-flipping arrow on doubled Unit cannot be in the image. -/
def flipMarker : (doubled Bool).obj smallGrade ⟶ (doubled Bool).obj smallGrade :=
  fun _ => TypeCat.ofHom (fun p => (!p.1,p.2))
example : ¬ ∃ f : smallGrade ⟶ smallGrade, (doubled Bool).map f = flipMarker := by
  rintro ⟨f,h⟩
  have h' := congrArg (fun k : (doubled Bool).obj smallGrade ⟶ (doubled Bool).obj smallGrade =>
      ((k false).hom (false,())).1) h
  exact Bool.noConfusion h'

example : ¬ ∃ s : Bool ⟶ Unit, s ≫ selectPoint true = 𝟙 _ := select_no_section true
def graded : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
example : ((doubled Unit).obj ((presheaf.map (selectPoint true).op).toFunctor.obj graded)) () =
    (Bool × Bool) := rfl
example : ((doubled Unit).obj ((presheaf.map (selectPoint false).op).toFunctor.obj graded)) () =
    (Bool × Empty) := rfl
example : (((doubled Bool).map widen false).hom (false,())) = (false,true) := rfl
open TaggedMixed.All
def z : ZeroPower.weighted presheaf Bool := pair _ _ ⟨Bool,rfl⟩ graded
example : (ZeroPower.eval presheaf Bool).obj z true = Bool := rfl
example : (ZeroPower.eval presheaf Bool).obj z false = Empty := rfl
noncomputable def u := (CoproductSpan.All.component splitEndpoints presheaf Bool 1).inverse.obj sourcePair
#check taggedDiagram splitEndpoints twice (selectPoint true)
#check taggedLaw splitEndpoints twice (selectPoint true) ⟨0,z⟩
#check taggedLaw splitEndpoints twice (selectPoint true) ⟨1,u⟩
end TaggedMixedProbe
