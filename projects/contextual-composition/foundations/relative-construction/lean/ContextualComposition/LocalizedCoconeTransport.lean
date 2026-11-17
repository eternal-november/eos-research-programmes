module
public import ContextualComposition.EquivalenceCoherence
@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

/-- The existing source presentation compared with functors from the chosen localization. -/
noncomputable def localizedCoconeEquivalence (e : K ⥤ C) (d : L ⥤ C) (D : Type uD) [Category.{vD} D] :
    ((Primitive.generators e d).Localization ⥤ D) ≌ Cocone e d (D := D) :=
  (Localization.functorEquivalence (Primitive.generators e d).Q (Primitive.generators e d) D).trans
    (explicitPresentationEquivalence e d)

noncomputable abbrev localizedCocone (G : (Primitive.generators e d).Localization ⥤ D) :=
  (localizedCoconeEquivalence e d D).functor.obj G

/-- Endpoint transport agrees with the earlier independent-cocone pullback, with the chosen
factorization isomorphism retained rather than made strict. -/
noncomputable def localizedCoconeEndpointIso (T : Data e d e' d')
    (G : (Primitive.generators e' d').Localization ⥤ D) :
    pullback T (localizedCocone G) ≅ localizedCocone (localizedFactorFunctor T ⋙ G) :=
  pullbackRestrictionIso T ((Primitive.generators e' d').Q ⋙ G)
    (postcompose_inverts e' d' _ (Localization.inverts _ _) G) ≪≫
  restrictIso _ (postcompose_inverts e d _ (Localization.inverts _ _) (localizedFactorFunctor T ⋙ G)) ((Functor.associator (factorFunctor T) (Primitive.generators e' d').Q G).symm ≪≫
    isoWhiskerRight (chosenLift T).comparison.symm G ≪≫
    Functor.associator (Primitive.generators e d).Q (localizedFactorFunctor T) G)

theorem localizedCoconeEndpoint_app (T : Data e d e' d')
    (G : (Primitive.generators e' d').Localization ⥤ D) (s : Object e d) :
    (localizedCoconeEndpointIso T G).hom.app s = G.map ((chosenLift T).comparison.inv.app s) := by
  change 𝟙 _ ≫ (𝟙 _ ≫ G.map _ ≫ 𝟙 _) = _
  simp
  rfl

/-- Target change on the localized source comparison. -/
noncomputable def localizedCoconeTargetIso
    (G : (Primitive.generators e d).Localization ⥤ D) (H : D ⥤ E) :
    postcompose e d (localizedCocone G) H ≅ localizedCocone (G ⋙ H) :=
  restrictionPostcomposeIso e d _ (postcompose_inverts e d _ (Localization.inverts _ _) G) H ≪≫
    restrictIso _ (postcompose_inverts e d _ (Localization.inverts _ _) (G ⋙ H)) (Functor.associator (Primitive.generators e d).Q G H)

theorem localizedCoconeTarget_app (G : (Primitive.generators e d).Localization ⥤ D)
    (H : D ⥤ E) (s : Object e d) :
    (localizedCoconeTargetIso G H).hom.app s = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

/-- The endpoint bridge is natural in arbitrary transformations, not only invertible ones. -/
theorem localizedCoconeEndpoint_naturality (T : Data e d e' d')
    {G J : (Primitive.generators e' d').Localization ⥤ D} (a : G ⟶ J) :
    (pullbackFunctor T).map ((localizedCoconeEquivalence e' d' D).functor.map a) ≫
      (localizedCoconeEndpointIso T J).hom =
    (localizedCoconeEndpointIso T G).hom ≫
      (localizedCoconeEquivalence e d D).functor.map (whiskerLeft (localizedFactorFunctor T) a) := by
  apply Transformation.ext; funext s
  change a.app ((Primitive.generators e' d').Q.obj ((factorFunctor T).obj s)) ≫
    (localizedCoconeEndpointIso T J).hom.app s =
    (localizedCoconeEndpointIso T G).hom.app s ≫ a.app _
  rw [localizedCoconeEndpoint_app, localizedCoconeEndpoint_app]
  exact (a.naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The new bridge respects the already constructed endpoint/target interchange square. -/
theorem localizedCocone_endpoint_target (T : Data e d e' d')
    (G : (Primitive.generators e' d').Localization ⥤ D) (H : D ⥤ E) :
    postcomposeMap e d H (localizedCoconeEndpointIso T G).hom ≫
      (localizedCoconeTargetIso (localizedFactorFunctor T ⋙ G) H).hom ≫
      (localizedCoconeEquivalence e d E).functor.map
        (Functor.associator (localizedFactorFunctor T) G H).hom =
    (pullbackPostcomposeIso T (localizedCocone G) H).hom ≫
      (pullbackFunctor T).map (localizedCoconeTargetIso G H).hom ≫
      (localizedCoconeEndpointIso T (G ⋙ H)).hom := by
  apply Transformation.ext; funext s
  change H.map ((localizedCoconeEndpointIso T G).hom.app s) ≫
      (localizedCoconeTargetIso (localizedFactorFunctor T ⋙ G) H).hom.app s ≫ 𝟙 _ =
    (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _)) ≫ (localizedCoconeTargetIso G H).hom.app ((factorFunctor T).obj s) ≫
      (localizedCoconeEndpointIso T (G ⋙ H)).hom.app s
  rw [localizedCoconeEndpoint_app, localizedCoconeEndpoint_app,
    localizedCoconeTarget_app, localizedCoconeTarget_app]
  simp
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Compatible endpoint choices agree through the bridge with the chosen localized choice map. -/
theorem localizedCocone_endpoint_choice {T U : Data e d e' d'} (a : ChoiceIso T U)
    (G : (Primitive.generators e' d').Localization ⥤ D) :
    (pullbackChoiceIso a (localizedCocone G)).hom ≫ (localizedCoconeEndpointIso U G).hom =
    (localizedCoconeEndpointIso T G).hom ≫
      (localizedCoconeEquivalence e d D).functor.map (whiskerRight (localizedChoiceIso a).hom G) := by
  apply Transformation.ext; funext s
  change (extensionFunctor e' d' (localizedCocone G)).map (a.factorIso.hom.app s) ≫
      (localizedCoconeEndpointIso U G).hom.app s =
    (localizedCoconeEndpointIso T G).hom.app s ≫
      G.map ((localizedChoiceIso a).hom.app ((Primitive.generators e d).Q.obj s))
  rw [localizedCoconeEndpoint_app, localizedCoconeEndpoint_app, localizedChoice_app]
  have h := (extensionRestrictionIso e' d' ((Primitive.generators e' d').Q ⋙ G)
    (postcompose_inverts e' d' _ (Localization.inverts _ _) G)).hom.naturality (a.factorIso.hom.app s)
  change (extensionFunctor e' d' (localizedCocone G)).map _ ≫ 𝟙 _ = 𝟙 _ ≫
    G.map ((Primitive.generators e' d').Q.map (a.factorIso.hom.app s)) at h
  simp only [Category.comp_id, Category.id_comp] at h
  rw [h]
  simp only [Functor.map_comp]
  erw [(G.mapIso ((chosenLift T).comparison.app s)).inv_hom_id_assoc]


set_option backward.isDefEq.respectTransparency false in
/-- Endpoint identity comparison is carried to the original cocone identity comparison. -/
theorem localizedCocone_endpoint_identity
    (G : (Primitive.generators e d).Localization ⥤ D) :
    (localizedCoconeEndpointIso (identityData e d) G).hom ≫
      (localizedCoconeEquivalence e d D).functor.map (whiskerRight localizedIdentityIso.hom G) ≫
      (localizedCoconeEquivalence e d D).functor.map (Functor.leftUnitor G).hom =
    (pullbackIdentityIso (localizedCocone G)).hom := by
  apply Transformation.ext; funext s
  change (localizedCoconeEndpointIso (identityData e d) G).hom.app s ≫
      G.map (localizedIdentityIso.hom.app ((Primitive.generators e d).Q.obj s)) ≫ 𝟙 _ =
    ((extensionFunctor e d (localizedCocone G)).map (factorIdentityIso.hom.app s) ≫ 𝟙 _) ≫ 𝟙 _
  rw [localizedCoconeEndpoint_app, localizedIdentity_app]
  have h := (extensionRestrictionIso e d ((Primitive.generators e d).Q ⋙ G)
    (postcompose_inverts e d _ (Localization.inverts _ _) G)).hom.naturality (factorIdentityIso.hom.app s)
  change (extensionFunctor e d (localizedCocone G)).map _ ≫ 𝟙 _ = 𝟙 _ ≫
    G.map ((Primitive.generators e d).Q.map (factorIdentityIso.hom.app s)) at h
  simp only [Category.comp_id, Category.id_comp] at h
  rw [h]
  simp only [Functor.map_comp, Category.comp_id]
  erw [(G.mapIso ((chosenLift (identityData e d)).comparison.app s)).inv_hom_id_assoc]

/-- The pointwise endpoint comparison assembles into an actual natural isomorphism. -/
noncomputable def localizedCoconeEndpointComparison (T : Data e d e' d') :
    (localizedCoconeEquivalence e' d' D).functor ⋙ pullbackFunctor T ≅
    (whiskeringLeft _ _ D).obj (localizedFactorFunctor T) ⋙
      (localizedCoconeEquivalence e d D).functor :=
  NatIso.ofComponents (localizedCoconeEndpointIso T) (fun a => localizedCoconeEndpoint_naturality T a)

set_option backward.isDefEq.respectTransparency false in
/-- Target change respects every transformation of localized functors. -/
theorem localizedCocone_target_naturality
    {G J : (Primitive.generators e d).Localization ⥤ D} (a : G ⟶ J) (H : D ⥤ E) :
    postcomposeMap e d H ((localizedCoconeEquivalence e d D).functor.map a) ≫
      (localizedCoconeTargetIso J H).hom =
    (localizedCoconeTargetIso G H).hom ≫
      (localizedCoconeEquivalence e d E).functor.map (whiskerRight a H) := by
  apply Transformation.ext; funext s
  change H.map (a.app _) ≫ (localizedCoconeTargetIso J H).hom.app s =
    (localizedCoconeTargetIso G H).hom.app s ≫ H.map (a.app _)
  rw [localizedCoconeTarget_app, localizedCoconeTarget_app]
  simp
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Target natural transformations commute with the same comparison. -/
theorem localizedCocone_target_transformation
    (G : (Primitive.generators e d).Localization ⥤ D) {H J : D ⥤ E} (a : H ⟶ J) :
    targetTransformation e d a (localizedCocone G) ≫ (localizedCoconeTargetIso G J).hom =
    (localizedCoconeTargetIso G H).hom ≫
      (localizedCoconeEquivalence e d E).functor.map (whiskerLeft G a) := by
  apply Transformation.ext; funext s
  change a.app _ ≫ (localizedCoconeTargetIso G J).hom.app s =
    (localizedCoconeTargetIso G H).hom.app s ≫ a.app _
  rw [localizedCoconeTarget_app, localizedCoconeTarget_app]
  simp
  erw [Category.comp_id]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The target bridge preserves the ordinary right unitor and cocone identity comparison. -/
theorem localizedCocone_target_identity (G : (Primitive.generators e d).Localization ⥤ D) :
    (localizedCoconeTargetIso G (𝟭 D)).hom ≫
      (localizedCoconeEquivalence e d D).functor.map (Functor.rightUnitor G).hom =
    (postcomposeIdIso e d (localizedCocone G)).hom := by
  apply Transformation.ext; funext s
  change (localizedCoconeTargetIso G (𝟭 D)).hom.app s ≫ 𝟙 _ = 𝟙 _
  rw [localizedCoconeTarget_app]
  exact Category.id_comp _

universe vF uF
variable {F : Type uF} [Category.{vF} F]
set_option backward.isDefEq.respectTransparency false in
/-- Target composition uses the ordinary associator, not a strict identification. -/
theorem localizedCocone_target_composition (G : (Primitive.generators e d).Localization ⥤ D)
    (H : D ⥤ E) (J : E ⥤ F) :
    (postcomposeCompIso e d (localizedCocone G) H J).hom ≫
      (localizedCoconeTargetIso G (H ⋙ J)).hom =
    postcomposeMap e d J (localizedCoconeTargetIso G H).hom ≫
      (localizedCoconeTargetIso (G ⋙ H) J).hom ≫
      (localizedCoconeEquivalence e d F).functor.map (Functor.associator G H J).hom := by
  apply Transformation.ext; funext s
  change 𝟙 _ ≫ (localizedCoconeTargetIso G (H ⋙ J)).hom.app s =
    J.map ((localizedCoconeTargetIso G H).hom.app s) ≫
      (localizedCoconeTargetIso (G ⋙ H) J).hom.app s ≫ 𝟙 _
  rw [localizedCoconeTarget_app, localizedCoconeTarget_app, localizedCoconeTarget_app]
  simp only [Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

universe vK'' vL'' uK'' uL''
variable {K'' : Type uK''} {L'' : Type uL''} [Category.{vK''} K''] [Category.{vL''} L'']
variable {e'' : K'' ⥤ C} {d'' : L'' ⥤ C}
set_option backward.isDefEq.respectTransparency false in
/-- Both composite endpoint routes use the original cocone and localized compositors. -/
theorem localizedCocone_endpoint_composition (T : Data e d e' d') (U : Data e' d' e'' d'')
    (G : (Primitive.generators e'' d'').Localization ⥤ D) :
    (pullbackCompositionIso T U (localizedCocone G)).hom ≫
      (localizedCoconeEndpointIso (composeData T U) G).hom =
    (pullbackFunctor T).map (localizedCoconeEndpointIso U G).hom ≫
      (localizedCoconeEndpointIso T (localizedFactorFunctor U ⋙ G)).hom ≫
      (localizedCoconeEquivalence e d D).functor.map
        (Functor.associator (localizedFactorFunctor T) (localizedFactorFunctor U) G).inv ≫
      (localizedCoconeEquivalence e d D).functor.map
        (whiskerRight (localizedCompositionIso T U).hom G) := by
  apply Transformation.ext; funext s
  change (𝟙 _ ≫ 𝟙 _ ≫ (extensionFunctor e'' d'' (localizedCocone G)).map
      ((factorCompositionIso T U).hom.app s)) ≫
    (localizedCoconeEndpointIso (composeData T U) G).hom.app s =
    (localizedCoconeEndpointIso U G).hom.app ((factorFunctor T).obj s) ≫
      (localizedCoconeEndpointIso T (localizedFactorFunctor U ⋙ G)).hom.app s ≫ 𝟙 _ ≫
      G.map ((localizedCompositionIso T U).hom.app ((Primitive.generators e d).Q.obj s))
  rw [localizedCoconeEndpoint_app, localizedCoconeEndpoint_app, localizedCoconeEndpoint_app,
    localizedComposition_app]
  have h := (extensionRestrictionIso e'' d'' ((Primitive.generators e'' d'').Q ⋙ G)
    (postcompose_inverts e'' d'' _ (Localization.inverts _ _) G)).hom.naturality
    ((factorCompositionIso T U).hom.app s)
  change (extensionFunctor e'' d'' (localizedCocone G)).map _ ≫ 𝟙 _ = 𝟙 _ ≫
    G.map ((Primitive.generators e'' d'').Q.map ((factorCompositionIso T U).hom.app s)) at h
  simp only [Category.comp_id, Category.id_comp] at h
  rw [h]
  simp only [Functor.comp_map, Functor.map_comp, Category.id_comp]
  erw [((localizedFactorFunctor U ⋙ G).mapIso ((chosenLift T).comparison.app s)).inv_hom_id_assoc]
  erw [(G.mapIso ((chosenLift U).comparison.app ((factorFunctor T).obj s))).inv_hom_id_assoc]

end ContextualComposition.Factorization.Endpoint
