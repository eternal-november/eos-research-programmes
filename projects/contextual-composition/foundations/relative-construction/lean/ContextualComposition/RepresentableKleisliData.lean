module
public import ContextualComposition.RepresentableYoneda
public import ContextualComposition.RepresentableComma
public import ContextualComposition.AmbientCoherentPseudomonad
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisli
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} (S : P.Split)
abbrev yObj (A : B) : Obj.{u,u} B := RepresentableYoneda.rep A
abbrev KObj (A : B) := obj.{u,u} S 1 (yObj A)
abbrev KH (A D : B) := yObj A ⟶ KObj S D
variable {S} {A D E : B}
local instance kleisliStrongCategory (F G : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{u,u}) : Category (StrongTrans F G) := StrongTrans.homCategory
def unpack' (Q : Obj.{u,u} B) (A : B) : (yObj A ⟶ Q) ⥤ RepresentableYoneda.Hom (underlying.{u,u} Q) A where
  obj f := f.hom
  map t := t.hom
def pack' (Q : Obj.{u,u} B) (A : B) : RepresentableYoneda.Hom (underlying.{u,u} Q) A ⥤ (yObj A ⟶ Q) where
  obj f := InducedBicategory.mkHom f
  map t := InducedBicategory.mkHom₂ t
def homModel (Q : Obj.{u,u} B) (A : B) : (yObj A ⟶ Q) ≌ RepresentableYoneda.Hom (underlying.{u,u} Q) A :=
  CategoryTheory.Equivalence.mk (unpack' Q A) (pack' Q A) (Iso.refl _) (Iso.refl _)
def fibreEquiv : KH S A D ≌ (underlying.{u,u} (KObj S D)).obj (op A) :=
  (homModel (KObj S D) A).trans (RepresentableYoneda.equivalence _ A)
def commaEquiv : KH S A D ≌ CostructuredArrow (P.extend A) D :=
  (fibreEquiv (S := S) (A := A) (D := D)).trans (RepresentableComma.iso (P.extend A) D).toEquivalence
def row (f : KH S A D) : RepresentableComma.Row (P.extend A) D := (fibreEquiv (S := S)).functor.obj f
noncomputable def unit (T : Data S) (A : B) : KH S A A := AmbientHorizontalFrames.E S (yObj A) T.unit
noncomputable def compose (T : Data S) (f : KH S A D) (g : KH S D E) : KH S A E :=
  (f ≫ AmbientBicategory.map S 1 g) ≫ AmbientHorizontalFrames.M S (yObj E) T.mult
noncomputable def composeCell (T : Data S) {f f' : KH S A D} {g g' : KH S D E} (t : f ⟶ f') (k : g ⟶ g') :
    compose T f g ⟶ compose T f' g' :=
  ((t ▷ AmbientBicategory.map S 1 g) ≫ f' ◁ AmbientBicategory.cell S 1 k) ▷ AmbientHorizontalFrames.M S (yObj E) T.mult
end ContextualComposition.GrothendieckStep.RepresentableKleisli
