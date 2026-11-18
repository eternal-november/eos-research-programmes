import ContextualComposition.TaggedMixed
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace Independent202
-- Pulling a set along any base map in Y leaves the set unchanged.
def Y : (Type)ᵒᵖ ⥤ Cat.{0,1} := (Functor.const _).obj (Cat.of Type)
def diag (A : Type) : Type ⥤ presheaf.obj (op A) where
  obj X := fun _ => X
  map h := fun _ => h
  map_id _ := rfl
  map_comp _ _ := rfl
-- Natural change into a *different* payload presheaf, not a self map.
def T : Y ⟶ presheaf where
  app A := (diag A.unop).toCatHom
  naturality _ _ _ := rfl
def indexReading : (diag Bool).obj Unit ⟶ (diag Bool).obj Bool :=
  fun b => TypeCat.ofHom (fun _ => b)
example : ¬ ∃ f : Unit ⟶ Bool, (diag Bool).map f = indexReading := by
  rintro ⟨f,h⟩
  have p := congrArg (fun k : (diag Bool).obj Unit ⟶ (diag Bool).obj Bool => ((k false).hom ())) h
  have q := congrArg (fun k : (diag Bool).obj Unit ⟶ (diag Bool).obj Bool => ((k true).hom ())) h
  exact Bool.noConfusion (p.symm.trans q)
example : ¬ ∃ s : Bool ⟶ Unit, s ≫ selectPoint false = 𝟙 Bool := select_no_section false
open TaggedMixed.All
def z : ZeroPower.weighted Y Bool := pair _ _ ⟨Bool,rfl⟩ Bool
def deep : (Iterates.layer endpoints splitEndpoints Y 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) Bool)
noncomputable def u2 := (CoproductSpan.All.component splitEndpoints Y Bool 2).inverse.obj deep
#check taggedDiagram splitEndpoints T (selectPoint false)
#check taggedLaw splitEndpoints T (selectPoint false) ⟨0,z⟩
#check taggedLaw splitEndpoints T (selectPoint false) ⟨2,u2⟩
example : ((T.app (op Bool)).toFunctor.obj ((ZeroPower.eval Y Bool).obj z)) true = Bool := rfl
end Independent202
