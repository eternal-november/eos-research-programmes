module
public import ContextualComposition.RepresentableYonedaFaces
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableYoneda
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open ContextadCoherence FibreValue
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe b u
variable {B : Type b} [Category.{u} B] {Q : Bᵒᵖ ⥤ Cat.{u,u}} {A : B}
local instance counitHomCat (F G : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{u,u}) : Category (StrongTrans F G) := StrongTrans.homCategory
theorem sqCast (F : Hom Q A) {D E : B} (a : E ⟶ D) {f g : D ⟶ A} (e : f = g) :
    eqToHom (congrArg (atPoint Q A F) (congrArg (a ≫ ·) e)) ≫ (sq F a g).hom =
      (sq F a f).hom ≫ (restrict (Q := Q) a).map (eqToHom (congrArg (atPoint Q A F) e)) := by
  subst g; simp
theorem sqExtend (x : Q.obj (op A)) {D E : B} (a : E ⟶ D) (f : D ⟶ A) :
    (sq (extend Q A x) a f).hom = eqToHom (Functor.congr_obj (strictComp Q a f) x) :=
  eqToHom_app (extendSquareEq Q A x a) (Discrete.mk f)
abbrev seed (F : Hom Q A) := (evaluate Q A).obj F
def counitAt (F : Hom Q A) {D : B} (f : D ⟶ A) :
    atPoint Q A F f ≅ atPoint Q A (extend Q A (seed F)) f :=
  eqToIso (congrArg (atPoint Q A F) (Category.comp_id f).symm) ≪≫ sq F f (𝟙 A)
theorem counitSquare (F : Hom Q A) {D E : B} (a : E ⟶ D) (f : D ⟶ A) :
    (counitAt F (a ≫ f)).hom ≫ (sq (extend Q A (seed F)) a f).hom =
      (sq F a f).hom ≫ (restrict (Q := Q) a).map (counitAt F f).hom := by
  rw [sqExtend]
  simp only [counitAt,Iso.trans_hom,eqToIso.hom,Category.assoc,Functor.map_comp]
  rw [← Category.assoc ((sq F a f).hom), ← sqCast F a (Category.comp_id f).symm]
  simp only [Category.assoc]
  exact (congrArg (eqToHom (congrArg (atPoint Q A F) (Category.comp_id (a ≫ f)).symm) ≫ ·)
    (associativity F f a (𝟙 A))).trans (by simp only [← Category.assoc,eqToHom_trans])
theorem pointCastNaturality {F G : Hom Q A} (t : F ⟶ G) {D : B} {f g : D ⟶ A} (e : f = g) :
    atCell Q A t f ≫ eqToHom (congrArg (atPoint Q A G) e) =
      eqToHom (congrArg (atPoint Q A F) e) ≫ atCell Q A t g := by
  subst g; simp
theorem counitNatural {F G : Hom Q A} (t : F ⟶ G) {D : B} (f : D ⟶ A) :
    atCell Q A t f ≫ (counitAt G f).hom =
      (counitAt F f).hom ≫ (restrict (Q := Q) f).map (atCell Q A t (𝟙 A)) := by
  simp only [counitAt,Iso.trans_hom,eqToIso.hom,← Category.assoc]
  rw [pointCastNaturality t (Category.comp_id f).symm, Category.assoc, modification t f (𝟙 A), Category.assoc]
end ContextualComposition.GrothendieckStep.RepresentableYoneda
