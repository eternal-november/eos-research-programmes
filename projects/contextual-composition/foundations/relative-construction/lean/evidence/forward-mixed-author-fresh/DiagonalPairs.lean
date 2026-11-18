import ContextualComposition.ForwardMixed
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace DiagonalPairs
def square (A : Type) : presheaf.obj (op A) ⥤ presheaf.obj (op A) where
  obj X := fun a => X a × X a
  map f := fun a => TypeCat.ofHom (fun p => ((f a).hom p.1,(f a).hom p.2))
  map_id _ := rfl
  map_comp _ _ := rfl
def T : presheaf ⟶ presheaf where
  app A := (square A.unop).toCatHom
  naturality _ _ _ := rfl
def swap : (square Bool).obj wideGrade ⟶ (square Bool).obj wideGrade :=
  fun _ => TypeCat.ofHom (fun p => (p.2,p.1))
-- A doubled map acts independently by the same function in both slots.
-- At first input true, the swap can produce both true and false.
example : ¬ ∃ f : wideGrade ⟶ wideGrade, (square Bool).map f = swap := by
  rintro ⟨f,h⟩
  have e := congrArg (fun k : (square Bool).obj wideGrade ⟶ (square Bool).obj wideGrade =>
    ((k true).hom (true,false)).1) h
  have g := congrArg (fun k : (square Bool).obj wideGrade ⟶ (square Bool).obj wideGrade =>
    ((k true).hom (true,true)).1) h
  exact Bool.noConfusion (e.symm.trans g)
def constantFalse : Bool ⟶ Bool := collapse ≫ selectPoint false
example : ¬ ∃ s : Bool ⟶ Bool, s ≫ constantFalse = 𝟙 _ := by
  rintro ⟨s,h⟩
  exact Bool.noConfusion (congrArg (fun k : Bool ⟶ Bool => k true) h)
def graded : presheaf.obj (op Bool) := fun a => if a then Empty else Bool
def z : ZeroPower.weighted presheaf Bool := pair _ _ ⟨Bool,rfl⟩ graded
def two : (Iterates.layer endpoints splitEndpoints presheaf 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) (fun _ => Bool))
noncomputable def v := (CoproductSpan.All.component splitEndpoints presheaf Bool 2).inverse.obj two
#check ForwardMixed.All.diagram splitEndpoints T constantFalse
#check ForwardMixed.All.law splitEndpoints T constantFalse ⟨0,z⟩
#check ForwardMixed.All.law splitEndpoints T constantFalse ⟨2,v⟩
#check ForwardMixed.strictCell (CoproductSpan.All.src splitEndpoints) (CoproductSpan.All.dst splitEndpoints)
  (SpanPull.All.parts splitEndpoints) T constantFalse 0 ((NativeCleavage.FibreTotal.into presheaf _ _ Bool).obj z)
example : ((presheaf.map constantFalse.op).toFunctor.obj ((square Bool).obj graded)) true = (Bool × Bool) := rfl
example : ((square Bool).obj graded) true = (Empty × Empty) := rfl
end DiagonalPairs
