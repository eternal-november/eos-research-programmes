module
public import ContextualComposition.ContextadStrong
public import ContextualComposition.ContextadRepresentable
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableYoneda
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open ContextadCoherence FibreValue
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe b u
variable {B : Type b} [Category.{u} B] (Q : Bᵒᵖ ⥤ Cat.{u,u}) (A : B)
abbrev rep (D : B) : Bᵒᵖ ⥤ Cat.{u,u} := ContextadRepresentable.rep D
abbrev Hom := StrongTrans (rep A).toPseudofunctor' Q.toPseudofunctor'
local instance homCat (F G : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{u,u}) : Category (StrongTrans F G) := StrongTrans.homCategory
def atPoint (F : Hom Q A) {D : B} (f : D ⟶ A) : Q.obj (op D) :=
  (F.app ⟨op D⟩).toFunctor.obj (Discrete.mk f)
def atCell {F G : Hom Q A} (k : F ⟶ G) {D : B} (f : D ⟶ A) : atPoint Q A F f ⟶ atPoint Q A G f :=
  (k.as.app ⟨op D⟩).toNatTrans.app (Discrete.mk f)
def evaluate : Hom Q A ⥤ Q.obj (op A) where
  obj F := atPoint Q A F (𝟙 A)
  map k := atCell Q A k (𝟙 A)
def extendAt (x : Q.obj (op A)) (D : B) : (rep A).obj (op D) ⥤ Q.obj (op D) :=
  Discrete.functor fun f => (Q.map f.op).toFunctor.obj x
theorem extendSquareEq (x : Q.obj (op A)) {D E : B} (a : E ⟶ D) :
    ((rep A).map a.op).toFunctor ⋙ extendAt Q A x E = extendAt Q A x D ⋙ (Q.map a.op).toFunctor := by
  fapply Functor.ext
  · intro f
    exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (Q.map_comp f.as.op a.op)) x
  · intro f g k
    have e : f = g := Discrete.ext (Discrete.eq_of_hom k)
    subst g
    have h : k = 𝟙 f := @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom (f : Discrete (D ⟶ A)) f) _ _
    subst k
    simp only [Functor.map_id,Category.id_comp,eqToHom_trans,eqToHom_refl]
def extendSquare (x : Q.obj (op A)) {D E : B} (a : E ⟶ D) := eqToIso (extendSquareEq Q A x a)
theorem pureFrame {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F = G) (x : C) : Pure ((eqToIso e).hom.app x) := ⟨Functor.congr_obj e x,eqToHom_app e x⟩
theorem pureSquare (x : Q.obj (op A)) {D E : B} (a : E ⟶ D) (f : (rep A).obj (op D)) :
    Pure ((extendSquare Q A x a).hom.app f) := pureFrame (extendSquareEq Q A x a) f
def extend (x : Q.obj (op A)) : Hom Q A :=
  ContextadStrong.assemble (G := rep A) (H := Q) (extendAt Q A x) (extendSquare Q A x)
    (fun D f => pureEq (pureComp (pureSquare Q A x (𝟙 D) f) ⟨_,eqToHom_app _ _⟩) (pureMap _ ⟨_,eqToHom_app _ _⟩))
    (fun a b f => pureEq (pureComp (pureSquare Q A x (a ≫ b) f) ⟨_,eqToHom_app _ _⟩)
      (pureComp (pureMap _ ⟨_,eqToHom_app _ _⟩) (pureComp (pureSquare Q A x a _) (pureMap _ (pureSquare Q A x b f)))))
theorem extendRead (x : Q.obj (op A)) {D : B} (f : D ⟶ A) : atPoint Q A (extend Q A x) f = (Q.map f.op).toFunctor.obj x := rfl
theorem unit (x : Q.obj (op A)) : (evaluate Q A).obj (extend Q A x) = x :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (Q.map_id (op A))) x
end ContextualComposition.GrothendieckStep.RepresentableYoneda
