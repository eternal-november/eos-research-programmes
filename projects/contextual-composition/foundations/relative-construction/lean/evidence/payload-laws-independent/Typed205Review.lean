import ContextualComposition.PayloadLaws
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace Typed205
def Y : (Type)ᵒᵖ ⥤ Cat.{0,1} := (Functor.const _).obj (Cat.of Type)
def diag (A : Type) : Type ⥤ presheaf.obj (op A) where
  obj X := fun _ => X
  map f := fun _ => f
  map_id _ := rfl
  map_comp _ _ := rfl
def T : Y ⟶ presheaf where
  app A := (diag A.unop).toCatHom
  naturality _ _ _ := rfl
def W : (Type)ᵒᵖ ⥤ Cat.{0,1} where
  obj A := Cat.of (A.unop → (Type × Type))
  map {A _} f := (Pi.comap (fun _ : A.unop => Type × Type) (fun a => f.unop a)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def distinguish (A : Type) : presheaf.obj (op A) ⥤ W.obj (op A) where
  obj X := fun a => (X a,Bool × X a)
  map f := fun a => (f a,TypeCat.ofHom (fun p => (p.1,(f a).hom p.2)))
  map_id _ := rfl
  map_comp _ _ := rfl
def U : presheaf ⟶ W where
  app A := (distinguish A.unop).toCatHom
  naturality _ _ _ := rfl
example : (((T ≫ U).app (op Bool)).toFunctor.obj Unit) false = (Unit, Bool × Unit) := rfl
def z : ZeroPower.weighted Y Bool := pair _ _ ⟨Bool,rfl⟩ Bool
def deep : (Iterates.layer endpoints splitEndpoints Y 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) Bool)
noncomputable def u2 := (CoproductSpan.All.component splitEndpoints Y Bool 2).inverse.obj deep
noncomputable def whole := (CoproductSpan.compare (CoproductSpan.All.src splitEndpoints)
    (CoproductSpan.All.dst splitEndpoints) Bool Y).obj
open PayloadLaws.All
#check strong splitEndpoints Bool
#check inverseComp splitEndpoints Bool T U
#check evaluationComp splitEndpoints Bool T U (whole ⟨0,z⟩)
#check evaluationComp splitEndpoints Bool T U (whole ⟨2,u2⟩)
#check evaluationUnit (Y := Y) splitEndpoints Bool (whole ⟨0,z⟩)
example : Cat.Hom.toNatIso ((strong splitEndpoints Bool).naturality ⟨T ≫ U⟩) =
    (SumChange.evaluationPayload splitEndpoints (T ≫ U) Bool).symm := rfl
end Typed205
namespace Consumer205
open CategoryTheory.Functor PayloadLaws.All CoproductSpan.All
universe b w
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (A : B)
  {Y Z W : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z) (U : Z ⟶ W)
example : ((strong R A).app ⟨Y⟩).toFunctor = (evaluation R Y A).functor := rfl
example : ((wholeAction R A).map T).toFunctor = ChainPayload.fibreMap T (CoproductSpan.wholeLeg (src R) (dst R) A) := rfl
example : ((iterateAction R A).map T).toFunctor = ((ChainPayload.allIterateMap T R).app (op A)).toFunctor := rfl
example :
    (SumChange.evaluationPayload R (T ≫ U) A).inv ≫ whiskerLeft (evaluation R Y A).functor (eqToHom (iterateComp R A T U)) =
      whiskerRight (eqToHom (wholeComp R A T U)) (evaluation R W A).functor ≫
        whiskerLeft (ChainPayload.fibreMap T (CoproductSpan.wholeLeg (src R) (dst R) A)) (SumChange.evaluationPayload R U A).inv ≫
        whiskerRight (SumChange.evaluationPayload R T A).inv ((ChainPayload.allIterateMap U R).app (op A)).toFunctor :=
  evaluationCompDiagram R A T U
end Consumer205
