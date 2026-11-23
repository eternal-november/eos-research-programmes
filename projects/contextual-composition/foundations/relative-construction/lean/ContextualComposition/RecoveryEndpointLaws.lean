module
public import ContextualComposition.RecoveryTargetLaws

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
open GrothendieckStep GrothendieckStep.FibreValue
universe vK vL vK' vL' vK'' vL'' vC vD uK uL uK' uL' uK'' uL'' uC uD
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {K'' : Type uK''} {L'' : Type uL''} {C : Type uC} {D : Type uD}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vK''} K''] [Category.{vL''} L''] [Category.{vC} C] [Category.{vD} D]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C} {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}

private noncomputable def pullIdentity : pullbackFunctor (identityData e d) (D := D) ≅ 𝟭 _ :=
  NatIso.ofComponents pullbackIdentityIso (by
    intro S V a
    apply Transformation.ext; funext s
    change a.app _ ≫ (((extensionFunctor e d V).map _ ≫ 𝟙 _) ≫ 𝟙 _) =
      (((extensionFunctor e d S).map _ ≫ 𝟙 _) ≫ 𝟙 _) ≫ a.app _
    dsimp only [extensionFunctor]
    simp only [Category.comp_id]
    exact ((extensionTransformation e d a).naturality (factorIdentityIso.hom.app s)).symm)

private noncomputable def pullComp (T : Data e d e' d') (U : Data e' d' e'' d'') :
    pullbackFunctor U (D := D) ⋙ pullbackFunctor T ≅ pullbackFunctor (composeData T U) :=
  NatIso.ofComponents (pullbackCompositionIso T U) (by
    intro S V a
    apply Transformation.ext; funext s
    change a.app _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ (extensionFunctor e'' d'' V).map _) =
      (𝟙 _ ≫ 𝟙 _ ≫ (extensionFunctor e'' d'' S).map _) ≫ a.app _
    dsimp only [extensionFunctor]
    simp only [Category.id_comp]
    exact ((extensionTransformation e'' d'' a).naturality ((factorCompositionIso T U).hom.app s)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The recovered functor transports along the actual localized identity comparison. -/
theorem coconeEndpointRecovery_identity (S : Cocone e d (D := D)) :
    (coconeEndpointRecovery (identityData e d)).hom.app S ≫
      whiskerRight localizedIdentityIso.hom ((localizedCoconeEquivalence e d D).inverse.obj S) ≫
      (Functor.leftUnitor ((localizedCoconeEquivalence e d D).inverse.obj S)).hom =
    (localizedCoconeEquivalence e d D).inverse.map (pullbackIdentityIso S).hom := by
  let a := localizedCoconeEndpointComparison (identityData e d) (D := D)
  let u := ((whiskeringLeft _ _ D).mapIso (localizedIdentityIso (e := e) (d := d)) ≪≫
    whiskeringLeftObjIdIso).hom
  let v := (pullIdentity (e := e) (d := d) (D := D)).hom
  have fwd : Paste.UnitLaw a.symm u v := by
    intro G
    change (localizedCoconeEndpointIso (identityData e d) G).inv ≫
      (pullbackIdentityIso (localizedCocone G)).hom = _
    rw [← localizedCocone_endpoint_identity G, Iso.inv_hom_id_assoc, ← Functor.map_comp]
    rfl
  have h := MateLaws.unit (localizedCoconeEquivalence e d D) a u v fwd S
  rw [← recovery_eq_mate] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse composite endpoint square pastes through the chosen localization compositor and the independent cocone compositor. -/
theorem coconeEndpointRecovery_composition (T : Data e d e' d') (U : Data e' d' e'' d'')
    (S : Cocone e'' d'' (D := D)) :
    (coconeEndpointRecovery (composeData T U)).hom.app S ≫
      (whiskerRight (localizedCompositionIso T U).inv ((localizedCoconeEquivalence e'' d'' D).inverse.obj S) ≫
        (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) _).hom) =
    (localizedCoconeEquivalence e d D).inverse.map (pullbackCompositionIso T U S).inv ≫
      (coconeEndpointRecovery T).hom.app (pullback U S) ≫
      whiskerLeft (localizedFactorFunctor T) ((coconeEndpointRecovery U).hom.app S) := by
  let a := localizedCoconeEndpointComparison T (D := D)
  let b := localizedCoconeEndpointComparison U (D := D)
  let c := localizedCoconeEndpointComparison (composeData T U) (D := D)
  let u := ((whiskeringLeft _ _ D).mapIso (localizedCompositionIso T U).symm ≪≫
    whiskeringLeftObjCompIso (localizedFactorFunctor T) (localizedFactorFunctor U)).hom
  let v := (pullComp T U (D := D)).inv
  have fwd : Paste.CompLaw c.symm a.symm b.symm u v := by
    intro G
    have eq : pullbackCompositionIso T U (localizedCocone G) ≪≫ localizedCoconeEndpointIso (composeData T U) G =
        (pullbackFunctor T).mapIso (localizedCoconeEndpointIso U G) ≪≫
        localizedCoconeEndpointIso T (localizedFactorFunctor U ⋙ G) ≪≫
        (localizedCoconeEquivalence e d D).functor.mapIso (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) G).symm ≪≫
        (localizedCoconeEquivalence e d D).functor.mapIso (isoWhiskerRight (localizedCompositionIso T U) G) :=
      Iso.ext (localizedCocone_endpoint_composition T U G)
    change (localizedCoconeEndpointIso (composeData T U) G).inv ≫ (pullbackCompositionIso T U (localizedCocone G)).inv =
      (localizedCoconeEquivalence e d D).functor.map
        (whiskerRight (localizedCompositionIso T U).inv G ≫ (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) G).hom) ≫
      (localizedCoconeEndpointIso T (localizedFactorFunctor U ⋙ G)).inv ≫ (pullbackFunctor T).map (localizedCoconeEndpointIso U G).inv
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, isoWhiskerRight_inv, Functor.map_comp, Category.assoc] using congrArg Iso.inv eq
  have h := MateLaws.comp (localizedCoconeEquivalence e d D) (localizedCoconeEquivalence e' d' D)
    (localizedCoconeEquivalence e'' d'' D) c a b u v fwd S
  simp only [← recovery_eq_mate] at h
  exact h

end ContextualComposition.Factorization.Endpoint
