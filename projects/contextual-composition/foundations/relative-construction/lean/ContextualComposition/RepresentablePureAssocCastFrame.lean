module
public import ContextualComposition.RepresentablePureCastTranslation
public import ContextualComposition.RepresentablePureAssociativity
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureAssocCastFrame
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliGeneric RepresentablePureAssociativity RepresentablePureCastTranslation
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : (X : C) → X ⟶ F.obj X)
variable (L : ∀ {X Y : C} (f : X ⟶ F.obj Y), cmp F μ (e X) f ≅ f)
variable {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

theorem cast
    (a : cmp F μ (cmp F μ (J F e f) (J F e g)) (J F e h) ≅ cmp F μ (J F e f) (cmp F μ (J F e g) (J F e h)))
    (law : a ≪≫ ws F μ (J F e f) (c F μ e L g h) ≪≫ c F μ e L f (g ≫ h) =
      wr F μ (c F μ e L f g) (J F e h) ≪≫ c F μ e L (f ≫ g) h ≪≫ whiskerRightIso (α_ f g h) (e W)) :
    a.hom ≫ cell F μ (𝟙 (J F e f)) (c F μ e L g h).hom ≫ (c F μ e L f (g ≫ h)).hom =
    cell F μ (c F μ e L f g).hom (𝟙 (J F e h)) ≫ (c F μ e L (f ≫ g) h).hom ≫
      eqToHom (congrArg (fun j => J F e j) (Category.assoc f g h)) :=
  association a (ws F μ (J F e f) (c F μ e L g h)) (c F μ e L f (g ≫ h))
    (wr F μ (c F μ e L f g) (J F e h)) (c F μ e L (f ≫ g) h) _ _ _ _
    (second F μ (J F e f) (c F μ e L g h).hom).symm
    (first F μ (c F μ e L f g).hom (J F e h)).symm
    (assocTail f g h (e W)) law

end ContextualComposition.GrothendieckStep.RepresentablePureAssocCastFrame
