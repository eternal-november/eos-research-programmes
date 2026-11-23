module
public import ContextualComposition.CoconeRecovery

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
set_option backward.isDefEq.respectTransparency false
universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

/-- The independent cocone presentation obtained by localizing directly at comma normalization. -/
noncomputable def commaCoconeEquivalence (e : K ⥤ C) (d : L ⥤ C) (D : Type uD) [Category.{vD} D] :
    (Comma e d ⥤ D) ≌ Cocone e d (D := D) :=
  (Primitive.universalProperty e d D).trans (explicitPresentationEquivalence e d)

noncomputable abbrev commaCocone (F : Comma e d ⥤ D) := (commaCoconeEquivalence e d D).functor.obj F

theorem normalizeThenInverts (F : Comma e d ⥤ D) :
    (Primitive.generators e d).IsInvertedBy (normalize e d ⋙ F) :=
  postcompose_inverts e d _ (Primitive.normalize_inverts e d) F

/-- Precomposition by the actual localized normalization gives the same represented cocone, via its localization comparison. -/
noncomputable def commaCoconeRouteIso (F : Comma e d ⥤ D) :
    localizedCocone (Primitive.localizedNormalize e d ⋙ F) ≅ commaCocone F :=
  restrictIso (postcompose_inverts e d _ (Localization.inverts _ _) _) (normalizeThenInverts F)
    ((Functor.associator (Primitive.generators e d).Q (Primitive.localizedNormalize e d) F).symm ≪≫
      isoWhiskerRight (normalizationFac e d) F)

theorem commaCoconeRoute_app (F : Comma e d ⥤ D) (s : Object e d) :
    (commaCoconeRouteIso F).hom.app s = F.map ((normalizationFac e d).hom.app s) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Naturality covers arbitrary transformations of comma diagrams, including noninvertible ones. -/
noncomputable def commaCoconeRoute :
    (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e d) ⋙ (localizedCoconeEquivalence e d D).functor ≅
      (commaCoconeEquivalence e d D).functor :=
  NatIso.ofComponents commaCoconeRouteIso (by
    intro F G a
    apply Transformation.ext; funext s
    change a.app _ ≫ (commaCoconeRouteIso G).hom.app s = (commaCoconeRouteIso F).hom.app s ≫ a.app _
    rw [commaCoconeRoute_app, commaCoconeRoute_app]
    exact (a.naturality ((normalizationFac e d).hom.app s)).symm)

/-- Comparison of the actual inverse presentation functors, obtained by mating the forward route. -/
noncomputable def commaCoconeInverseRoute :
    (localizedCoconeEquivalence e d D).inverse ≅
      (commaCoconeEquivalence e d D).inverse ⋙ (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e d) :=
  (Functor.leftUnitor _).symm ≪≫ recoverySquare (commaCoconeEquivalence e d D) (localizedCoconeEquivalence e d D) _ (𝟭 _)
    (commaCoconeRoute ≪≫ (Functor.rightUnitor _).symm)

/-- This inverse comparison has the counit of the packaged comma presentation and the counit of the packaged localization presentation. -/
theorem commaCoconeInverseRoute_counit (S : Cocone e d (D := D)) :
    (localizedCoconeEquivalence e d D).functor.map (commaCoconeInverseRoute.hom.app S) ≫
      (commaCoconeRouteIso ((commaCoconeEquivalence e d D).inverse.obj S)).hom ≫
      (commaCoconeEquivalence e d D).counitIso.hom.app S =
    (localizedCoconeEquivalence e d D).counitIso.hom.app S := by
  let P := commaCoconeEquivalence e d D
  let Q := localizedCoconeEquivalence e d D
  let f := (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e d)
  let a := commaCoconeRoute ≪≫ (Functor.rightUnitor P.functor).symm
  have h := recoverySquare_counit P Q f (𝟭 _) a S
  simp only [a, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.id_map] at h
  erw [Category.comp_id] at h
  simp only [commaCoconeInverseRoute, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp]
  exact h

/-- Unit compatibility uses the chosen units of both presentation equivalences. -/
theorem commaCoconeInverseRoute_unit (F : Comma e d ⥤ D) :
    (localizedCoconeEquivalence e d D).unitIso.hom.app (Primitive.localizedNormalize e d ⋙ F) ≫
      (localizedCoconeEquivalence e d D).inverse.map (commaCoconeRouteIso F).hom ≫
      commaCoconeInverseRoute.hom.app (commaCocone F) =
    whiskerLeft (Primitive.localizedNormalize e d) ((commaCoconeEquivalence e d D).unitIso.hom.app F) := by
  let P := commaCoconeEquivalence e d D
  let Q := localizedCoconeEquivalence e d D
  let f := (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e d)
  let a := commaCoconeRoute ≪≫ (Functor.rightUnitor P.functor).symm
  have h := recoverySquare_unit P Q f (𝟭 _) a F
  simp only [a, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app] at h
  erw [Category.comp_id] at h
  simp only [commaCoconeInverseRoute, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp]
  exact h

/-- Target action on the direct comma presentation, with its ordinary associator. -/
noncomputable def commaCoconeTargetIso (F : Comma e d ⥤ D) (H : D ⥤ E) :
    postcompose e d (commaCocone F) H ≅ commaCocone (F ⋙ H) :=
  restrictionPostcomposeIso e d (normalize e d ⋙ F) (normalizeThenInverts F) H ≪≫
    restrictIso _ (normalizeThenInverts (F ⋙ H)) (Functor.associator (normalize e d) F H)

theorem commaCocone_route_target (F : Comma e d ⥤ D) (H : D ⥤ E) :
    postcomposeMap e d H (commaCoconeRouteIso F).hom ≫ (commaCoconeTargetIso F H).hom =
    (localizedCoconeTargetIso (Primitive.localizedNormalize e d ⋙ F) H).hom ≫
      (localizedCoconeEquivalence e d E).functor.map (Functor.associator (Primitive.localizedNormalize e d) F H).hom ≫
      (commaCoconeRouteIso (F ⋙ H)).hom := by
  apply Transformation.ext; funext s
  change H.map ((commaCoconeRouteIso F).hom.app s) ≫ (𝟙 _ ≫ 𝟙 _) =
    (localizedCoconeTargetIso _ H).hom.app s ≫ 𝟙 _ ≫ (commaCoconeRouteIso (F ⋙ H)).hom.app s
  rw [commaCoconeRoute_app, localizedCoconeTarget_app, commaCoconeRoute_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.id_comp]
  rfl

/-- Endpoint action on the direct comma presentation retains its raw normalization square. -/
noncomputable def commaCoconeEndpointIso (T : Data e d e' d') (F : Comma e' d' ⥤ D) :
    pullback T (commaCocone F) ≅ commaCocone (commaFunctor T ⋙ F) :=
  pullbackRestrictionIso T (normalize e' d' ⋙ F) (normalizeThenInverts F) ≪≫
    restrictIso _ (normalizeThenInverts (commaFunctor T ⋙ F))
      ((Functor.associator (factorFunctor T) (normalize e' d') F).symm ≪≫
        isoWhiskerRight (normalizationIso T) F ≪≫ Functor.associator (normalize e d) (commaFunctor T) F)

theorem commaCoconeEndpoint_app (T : Data e d e' d') (F : Comma e' d' ⥤ D) (s : Object e d) :
    (commaCoconeEndpointIso T F).hom.app s = F.map ((normalizationIso T).hom.app s) := by
  change 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- Both endpoint comparison routes use the chosen localized normalization square and its actual lift comparison. -/
theorem commaCocone_route_endpoint (T : Data e d e' d') (F : Comma e' d' ⥤ D) :
    (pullbackFunctor T).map (commaCoconeRouteIso F).hom ≫ (commaCoconeEndpointIso T F).hom =
    (localizedCoconeEndpointIso T (Primitive.localizedNormalize e' d' ⋙ F)).hom ≫
      (localizedCoconeEquivalence e d D).functor.map
        (((Functor.associator (localizedFactorFunctor T) (Primitive.localizedNormalize e' d') F).symm ≪≫
          isoWhiskerRight (localizedNormalizationIso T) F ≪≫ Functor.associator (Primitive.localizedNormalize e d) (commaFunctor T) F).hom) ≫
      (commaCoconeRouteIso (commaFunctor T ⋙ F)).hom := by
  apply Transformation.ext; funext s
  change (commaCoconeRouteIso F).hom.app ((factorFunctor T).obj s) ≫ (commaCoconeEndpointIso T F).hom.app s =
    (localizedCoconeEndpointIso T (Primitive.localizedNormalize e' d' ⋙ F)).hom.app s ≫
      (𝟙 _ ≫ F.map ((localizedNormalizationIso T).hom.app ((Primitive.generators e d).Q.obj s)) ≫ 𝟙 _) ≫
      (commaCoconeRouteIso (commaFunctor T ⋙ F)).hom.app s
  rw [commaCoconeRoute_app, commaCoconeEndpoint_app, localizedCoconeEndpoint_app, localizedNormalization_app, commaCoconeRoute_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  erw [← F.map_comp_assoc, ← (Primitive.localizedNormalize e' d').map_comp,
    Iso.inv_hom_id_app, Functor.map_id, Functor.map_id, Category.id_comp]
  let i := ((commaFunctor T) ⋙ F).mapIso ((normalizationFac e d).app s)
  erw [show F.map ((commaFunctor T).map ((normalizationFac e d).inv.app s)) ≫
    F.map ((commaFunctor T).map ((normalizationFac e d).hom.app s)) = 𝟙 _ from i.inv_hom_id,
    Category.comp_id]

end ContextualComposition.Factorization.Endpoint
