module
public import ContextualComposition.WeakChoiceCoherence
@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor
universe vK vL vK' vL' vK'' vL'' vC uK uL uK' uL' uK'' uL'' uC
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {K'' : Type uK''} {L'' : Type uL''} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vK''} K''] [Category.{vL''} L''] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}

/-- The normalization comparison uses the established chosen lift. -/
noncomputable def normalizationFac (e : K ⥤ C) (d : L ⥤ C) :
    (Primitive.generators e d).Q ⋙ Primitive.localizedNormalize e d ≅ normalize e d :=
  Localization.fac _ (Primitive.normalize_inverts e d) (Primitive.generators e d).Q

/-- Exact formula for the already constructed localized normalization square. -/
theorem localizedNormalization_app (T : Data e d e' d') (s : Object e d) :
    (localizedNormalizationIso T).hom.app ((Primitive.generators e d).Q.obj s) =
      (Primitive.localizedNormalize e' d').map ((chosenLift T).comparison.hom.app s) ≫
      (normalizationFac e' d').hom.app ((factorFunctor T).obj s) ≫
      (normalizationIso T).hom.app s ≫
      (commaFunctor T).map ((normalizationFac e d).inv.app s) := by
  dsimp only [localizedNormalizationIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  dsimp only [chosenLift, normalizationFac, localizedFactorFunctor, Primitive.localizedNormalize]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem localized_normalization_choice {T U : Data e d e' d'} (a : ChoiceIso T U) :
    whiskerRight (localizedChoiceIso a).hom (Primitive.localizedNormalize e' d') ≫
      (localizedNormalizationIso U).hom =
    (localizedNormalizationIso T).hom ≫
      whiskerLeft (Primitive.localizedNormalize e d) a.commaIso.hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, localizedChoice_app, localizedNormalization_app]
  dsimp only [chosenLift, normalizationFac, localizedFactorFunctor, Primitive.localizedNormalize]
  simp only [Functor.map_comp, Category.assoc]
  erw [((Primitive.localizedNormalize e' d').mapIso ((chosenLift U).comparison.app s)).inv_hom_id_assoc]
  erw [(normalizationFac e' d').hom.naturality_assoc (a.factorIso.hom.app s)]
  dsimp only [normalizationFac, Primitive.localizedNormalize, Functor.comp_map]
  erw [← Category.assoc ((normalize e' d').map (a.factorIso.hom.app s)), a.normalization_naturality]
  simp only [Category.assoc]
  erw [a.commaIso.hom.naturality ((normalizationFac e d).inv.app s)]
  rfl



set_option backward.isDefEq.respectTransparency false in
theorem localized_normalization_identity :
    whiskerRight localizedIdentityIso.hom (Primitive.localizedNormalize e d) ≫
      (Functor.leftUnitor (Primitive.localizedNormalize e d)).hom =
    (localizedNormalizationIso (identityData e d)).hom ≫
      whiskerLeft (Primitive.localizedNormalize e d) commaIdentityIso.hom ≫
      (Functor.rightUnitor (Primitive.localizedNormalize e d)).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, localizedIdentity_app, localizedNormalization_app]
  dsimp only [chosenLift, normalizationFac, localizedFactorFunctor, Primitive.localizedNormalize]
  simp only [Functor.map_comp, Category.assoc]
  erw [commaIdentityIso.hom.naturality_assoc ((normalizationFac e d).inv.app s)]
  dsimp only [Functor.id_map]
  erw [← Category.assoc ((normalizationIso (identityData e d)).hom.app s), ← normalization_identity]
  erw [← (normalizationFac e d).hom.naturality_assoc (factorIdentityIso.hom.app s)]
  dsimp only [normalizationFac, Primitive.localizedNormalize, Functor.comp_map, Functor.id_obj]
  simp only [Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem localized_normalization_composition (T : Data e d e' d') (U : Data e' d' e'' d'') :
    whiskerRight (localizedCompositionIso T U).hom (Primitive.localizedNormalize e'' d'') ≫
      (localizedNormalizationIso (composeData T U)).hom =
    (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) (Primitive.localizedNormalize e'' d'')).hom ≫
      whiskerLeft (localizedFactorFunctor T) (localizedNormalizationIso U).hom ≫
      (Functor.associator (localizedFactorFunctor T) (Primitive.localizedNormalize e' d') (commaFunctor U)).inv ≫
      whiskerRight (localizedNormalizationIso T).hom (commaFunctor U) ≫
      (Functor.associator (Primitive.localizedNormalize e d) (commaFunctor T) (commaFunctor U)).hom ≫
      whiskerLeft (Primitive.localizedNormalize e d) (commaCompositionIso T U).hom := by
  apply Descent.ext (Q := (Primitive.generators e d).Q) (W := Primitive.generators e d)
  intro s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, localizedComposition_app, localizedNormalization_app]
  dsimp only [chosenLift, normalizationFac, localizedFactorFunctor, Primitive.localizedNormalize]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp]
  erw [((Primitive.localizedNormalize e'' d'').mapIso ((chosenLift (composeData T U)).comparison.app s)).inv_hom_id_assoc]
  erw [(normalizationFac e'' d'').hom.naturality_assoc ((factorCompositionIso T U).hom.app s)]
  dsimp only [normalizationFac, Primitive.localizedNormalize, Functor.comp_map]
  erw [normalization_composition T U s]
  simp only [Category.assoc]
  erw [((normalize e'' d'').mapIso ((factorCompositionIso T U).app s)).hom_inv_id_assoc]
  erw [← (localizedNormalizationIso U).hom.naturality_assoc ((chosenLift T).comparison.hom.app s)]
  erw [localizedNormalization_app]
  dsimp only [chosenLift, normalizationFac, localizedFactorFunctor, Primitive.localizedNormalize, Functor.comp_map]
  simp only [Category.assoc]
  erw [((commaFunctor U).mapIso ((normalizationFac e' d').app ((factorFunctor T).obj s))).inv_hom_id_assoc]
  erw [(commaCompositionIso T U).hom.naturality ((normalizationFac e d).inv.app s)]
  rfl

/-- Section transport uses the specific source-lift balance and the chosen transport factorization. -/
noncomputable def sectionTransportIso (T : Data e d e' d') :
    commaFunctor T ⋙ Primitive.localizedSection e' d' ≅
      Primitive.localizedSection e d ⋙ localizedFactorFunctor T :=
  (Functor.associator (commaFunctor T) (sectionFunctor e' d') (Primitive.generators e' d').Q).symm ≪≫
    localizedSectionComparison T ≪≫
    Functor.associator (sectionFunctor e d) (factorFunctor T) (Primitive.generators e' d').Q ≪≫
    isoWhiskerLeft (sectionFunctor e d) (chosenLift T).comparison.symm ≪≫
    (Functor.associator (sectionFunctor e d) (Primitive.generators e d).Q (localizedFactorFunctor T)).symm

theorem sectionTransport_app (T : Data e d e' d') (s : Comma e d) :
    (sectionTransportIso T).hom.app s =
      (Primitive.generators e' d').Q.map ((sectionComparison T).app s) ≫
        (chosenLift T).comparison.inv.app ((sectionFunctor e d).obj s) := by
  dsimp only [sectionTransportIso, localizedSectionComparison]
  dsimp only [Primitive.localizedSection, chosenLift, localizedFactorFunctor]
  simp [asIso]

set_option backward.isDefEq.respectTransparency false in
theorem section_transport_choice {T U : Data e d e' d'} (a : ChoiceIso T U) :
    whiskerRight a.commaIso.hom (Primitive.localizedSection e' d') ≫ (sectionTransportIso U).hom =
      (sectionTransportIso T).hom ≫ whiskerLeft (Primitive.localizedSection e d) (localizedChoiceIso a).hom := by
  apply NatTrans.ext; funext s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, sectionTransport_app]
  dsimp only [Primitive.localizedSection, Functor.comp_obj, Functor.comp_map]
  rw [localizedChoice_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e' d').Q.map) (a.section_naturality s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc, h]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem section_transport_identity :
    (sectionTransportIso (identityData e d)).hom ≫
      whiskerLeft (Primitive.localizedSection e d) localizedIdentityIso.hom ≫
      (Functor.rightUnitor (Primitive.localizedSection e d)).hom =
    whiskerRight commaIdentityIso.hom (Primitive.localizedSection e d) ≫
      (Functor.leftUnitor (Primitive.localizedSection e d)).hom := by
  apply NatTrans.ext; funext s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, sectionTransport_app]
  dsimp only [Primitive.localizedSection, Functor.comp_obj, Functor.comp_map]
  rw [localizedIdentity_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e d).Q.map) (section_identity s)
  simp only [Functor.map_comp] at h
  erw [← Category.assoc, h]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem section_transport_composition (T : Data e d e' d') (U : Data e' d' e'' d'') :
    (sectionTransportIso (composeData T U)).hom =
      whiskerRight (commaCompositionIso T U).inv (Primitive.localizedSection e'' d'') ≫
      (Functor.associator (commaFunctor T) (commaFunctor U) (Primitive.localizedSection e'' d'')).hom ≫
      whiskerLeft (commaFunctor T) (sectionTransportIso U).hom ≫
      (Functor.associator (commaFunctor T) (Primitive.localizedSection e' d') (localizedFactorFunctor U)).inv ≫
      whiskerRight (sectionTransportIso T).hom (localizedFactorFunctor U) ≫
      (Functor.associator (Primitive.localizedSection e d) (localizedFactorFunctor T) (localizedFactorFunctor U)).hom ≫
      whiskerLeft (Primitive.localizedSection e d) (localizedCompositionIso T U).hom := by
  apply NatTrans.ext; funext s
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, sectionTransport_app]
  dsimp only [Primitive.localizedSection, Functor.comp_obj, Functor.comp_map]
  rw [localizedComposition_app]
  dsimp only [chosenLift, localizedFactorFunctor]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp]
  erw [((localizedFactorFunctor U).mapIso ((chosenLift T).comparison.app ((sectionFunctor e d).obj s))).inv_hom_id_assoc]
  erw [← (chosenLift U).comparison.inv.naturality_assoc ((sectionComparison T).app s)]
  dsimp only [chosenLift, localizedFactorFunctor, Functor.comp_map]
  dsimp only [Functor.comp_obj]
  simp only [Iso.inv_hom_id_app_assoc]
  have h := congrArg ((Primitive.generators e'' d'').Q.map) (section_composition T U s)
  simp only [Functor.map_comp] at h
  erw [h]
  simp only [Category.assoc]

end ContextualComposition.Factorization.Endpoint
