module
public import ContextualComposition.RepresentableYonedaData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableYoneda
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open ContextadCoherence FibreValue
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe b u
variable {B : Type b} [Category.{u} B] {Q : Bᵒᵖ ⥤ Cat.{u,u}} {A : B}
local instance facesHomCat (F G : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{u,u}) : Category (StrongTrans F G) := StrongTrans.homCategory
abbrev restrict {E D : B} (a : E ⟶ D) : Q.obj (op D) ⥤ Q.obj (op E) := (Q.map a.op).toFunctor
def sq (F : Hom Q A) {D E : B} (a : E ⟶ D) (f : D ⟶ A) :
    atPoint Q A F (a ≫ f) ≅ (restrict (Q := Q) a).obj (atPoint Q A F f) :=
  (Cat.Hom.toNatIso (F.naturality ⟨a.op⟩)).app (Discrete.mk f)
theorem associativity (F : Hom Q A) {D E J : B} (a : E ⟶ D) (b : J ⟶ E) (f : D ⟶ A) :
    (sq F (b ≫ a) f).hom ≫ eqToHom (Functor.congr_obj (strictComp Q b a) (atPoint Q A F f)) =
    eqToHom (congrArg (atPoint Q A F) (Category.assoc b a f)) ≫
      (sq F b (a ≫ f)).hom ≫ (restrict (Q := Q) b).map (sq F a f).hom := by
  have h := congrArg (fun k => Cat.Hom₂.toNatTrans k |>.app (Discrete.mk f)) (F.naturality_comp ⟨a.op⟩ ⟨b.op⟩)
  simp only [Cat.Hom₂.comp_app,Cat.whiskerLeft_app,Cat.whiskerRight_app,
    Cat.associator_hom_toNatTrans,Cat.associator_inv_toNatTrans,Functor.associator_hom_app,Functor.associator_inv_app,
    Functor.toPseudofunctor'_mapComp, eqToIso.hom,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app,eqToHom_map] at h
  change (sq F (b ≫ a) f).hom ≫ eqToHom (Functor.congr_obj (strictComp Q b a) (atPoint Q A F f)) =
    eqToHom (congrArg (atPoint Q A F) (Category.assoc b a f)) ≫
      𝟙 _ ≫ (sq F b (a ≫ f)).hom ≫ 𝟙 _ ≫ (restrict (Q := Q) b).map (sq F a f).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp,Category.comp_id] using h
theorem modification {F G : Hom Q A} (t : F ⟶ G) {D E : B} (a : E ⟶ D) (f : D ⟶ A) :
    atCell Q A t (a ≫ f) ≫ (sq G a f).hom =
      (sq F a f).hom ≫ (restrict (Q := Q) a).map (atCell Q A t f) := by
  exact congrArg (fun k => Cat.Hom₂.toNatTrans k |>.app (Discrete.mk f)) (t.as.naturality ⟨a.op⟩)
end ContextualComposition.GrothendieckStep.RepresentableYoneda
