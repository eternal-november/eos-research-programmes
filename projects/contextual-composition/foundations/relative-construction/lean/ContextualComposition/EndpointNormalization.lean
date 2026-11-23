module
public import ContextualComposition.EndpointPseudofunctors
public import ContextualComposition.EndpointUniverse
public import ContextualComposition.EquivalenceCoherence
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Presentation
open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe vK vL vC uK uL uC
variable (C : Type uC) [Category.{vC} C]

/-- The two actions land in a common category universe through the explicit small-category equivalences. -/
noncomputable abbrev largeLocalization := (localizedPseudo.{vK,vL,vC,uK,uL,uC} C).comp
  UniverseLift.pseudofunctor.{max vK vL vC uK uL uC}
abbrev largeComma := (commaPseudo.{vK,vL,vC,uK,uL,uC} C).comp
  UniverseLift.pseudofunctor.{max vK vL vC uK uL uC}

private theorem slide {A : Type*} [Category* A] {x y z w : A} (i : x ≅ y) (j : z ≅ w)
    (f : y ⟶ w) (g : x ⟶ z) (h : i.hom ≫ f = g ≫ j.hom) : f ≫ j.inv = i.inv ≫ g := by
  apply (cancel_epi i.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def normalization : Pseudofunctor.StrongTrans (largeLocalization.{vK,vL,vC,uK,uL,uC} C) (largeComma C) where
  app A := (UniverseLift.map (Primitive.localizedNormalize A.source A.target)).toCatHom
  naturality T := Cat.Hom.isoMk (UniverseLift.iso (localizedNormalizationIso T))
  naturality_naturality η := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    exact NatTrans.congr_app (localized_normalization_choice η) (ULift.down x)
  naturality_id A := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    have h := NatTrans.congr_app (localized_normalization_identity (e := A.source) (d := A.target)) (ULift.down x)
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at h
    erw [Category.comp_id, Category.comp_id] at h
    change _ ≫ (_ ≫ 𝟙 _) = (Primitive.localizedNormalize A.source A.target).map (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.comp_id]
    exact h.symm
  naturality_comp T U := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    have h := NatTrans.congr_app (localized_normalization_composition T U) (ULift.down x)
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app] at h
    simp only [Category.id_comp] at h
    change _ ≫ (_ ≫ 𝟙 _) = (Primitive.localizedNormalize _ _).map (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.comp_id, Category.comp_id, Category.id_comp, Category.id_comp, Category.comp_id]
    apply slide ((Primitive.localizedNormalize _ _).mapIso ((localizedCompositionIso T U).app (ULift.down x)))
      ((commaCompositionIso T U).app ((Primitive.localizedNormalize _ _).obj (ULift.down x))) _ _
    rw [Category.assoc]
    exact h

noncomputable def sectionTransformation : Pseudofunctor.StrongTrans (largeComma.{vK,vL,vC,uK,uL,uC} C) (largeLocalization C) where
  app A := (UniverseLift.map (Primitive.localizedSection A.source A.target)).toCatHom
  naturality T := Cat.Hom.isoMk (UniverseLift.iso (sectionTransportIso T))
  naturality_naturality η := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    exact NatTrans.congr_app (section_transport_choice η) (ULift.down x)
  naturality_id A := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    have h := NatTrans.congr_app (section_transport_identity (e := A.source) (d := A.target)) (ULift.down x)
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at h
    erw [Category.comp_id, Category.comp_id] at h
    change _ ≫ (_ ≫ 𝟙 _) = (Primitive.localizedSection A.source A.target).map (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    erw [Category.comp_id, Category.comp_id, Category.comp_id]
    exact h
  naturality_comp T U := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply ULift.ext
    have h := NatTrans.congr_app (section_transport_composition T U) (ULift.down x)
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app] at h
    simp only [Category.id_comp] at h
    change _ ≫ (_ ≫ 𝟙 _) = (Primitive.localizedSection _ _).map (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.comp_id, Category.comp_id, Category.id_comp, Category.id_comp, Category.comp_id]
    change (sectionTransportIso (composeData T U)).hom.app (ULift.down x) ≫ (localizedCompositionIso T U).inv.app _ = _
    erw [h]
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app, Category.comp_id]
    rfl

end ContextualComposition.Factorization.Endpoint.Presentation
