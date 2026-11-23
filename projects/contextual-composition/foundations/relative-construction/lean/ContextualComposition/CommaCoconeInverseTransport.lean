module
public import ContextualComposition.CommaCoconeComparison
public import ContextualComposition.RecoveryTargetLaws

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
open GrothendieckStep GrothendieckStep.FibreValue
set_option backward.isDefEq.respectTransparency false

section Transport
variable {A B A' B' Y Y' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B'] [Category* Y] [Category* Y']
variable (P : A ≌ Y) (Q : B ≌ Y) (P' : A' ≌ Y') (Q' : B' ≌ Y')
variable (f : A ⥤ B) (k : A' ⥤ B') (a : A ⥤ A') (b : B ⥤ B') (j : Y ⥤ Y')
variable (c : f ⋙ Q.functor ≅ P.functor) (d : k ⋙ Q'.functor ≅ P'.functor)
variable (s : P.functor ⋙ j ≅ a ⋙ P'.functor) (t : Q.functor ⋙ j ≅ b ⋙ Q'.functor)
variable (u : f ⋙ b ⟶ a ⋙ k)

/-- A presentation route compared before and after a transport at the same represented target yields the inverse transport equation on its two actual recovery squares. -/
theorem recovery_route_transport
    (coh : ∀ x, j.map (c.hom.app x) ≫ s.hom.app x =
      t.hom.app (f.obj x) ≫ Q'.functor.map (u.app x) ≫ d.hom.app (a.obj x))
    (y : Y) :
    ((recoverySquare Q Q' b j t.symm).hom.app y ≫
      b.map ((recoverySquare P Q f (𝟭 Y) (c ≪≫ (Functor.rightUnitor _).symm)).hom.app y)) ≫
      u.app (P.inverse.obj y) =
    (recoverySquare P' Q' k (𝟭 Y') (d ≪≫ (Functor.rightUnitor _).symm)).hom.app (j.obj y) ≫
      k.map ((recoverySquare P P' a j s.symm).hom.app y) := by
  let l := (Functor.rightUnitor P.functor) ≪≫ c.symm
  let r := (Functor.rightUnitor P'.functor) ≪≫ d.symm
  let v := (Functor.leftUnitor j ≪≫ (Functor.rightUnitor j).symm).hom
  let diag : P.functor ⋙ (𝟭 Y ⋙ j) ≅ (f ⋙ b) ⋙ Q'.functor :=
    (Functor.associator P.functor (𝟭 Y) j).symm ≪≫ isoWhiskerRight l j ≪≫
      Functor.associator f Q.functor j ≪≫ isoWhiskerLeft f t ≪≫ (Functor.associator f b Q'.functor).symm
  have first : Paste.CompLaw diag.symm t.symm l.symm (𝟙 _) (𝟙 _) := by
    intro x
    simp [diag]
  have second : Paste.CompLaw diag.symm r.symm s.symm u v := by
    intro x
    have eq := coh x
    apply (cancel_epi (t.hom.app (f.obj x))).mp
    apply (cancel_mono (s.hom.app x)).mp
    simp only [diag, l, r, v, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
      whiskerLeft_app, whiskerRight_app, Functor.id_map,
      Category.assoc, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    erw [Category.id_comp, Category.comp_id]
    exact eq
  have h₁ := MateLaws.comp Q' Q P diag t l (𝟙 _) (𝟙 _) first y
  have h₂ := MateLaws.comp Q' P' P diag r s u v second y
  simp only [← recovery_eq_mate, Iso.symm_hom, Iso.symm_inv, NatTrans.id_app, Functor.map_id, Category.id_comp] at h₁ h₂
  have firstPath := (Category.comp_id ((recoverySquare P Q' _ _ diag.symm).hom.app y)).symm.trans h₁
  rw [firstPath] at h₂
  have hv : v.app y = 𝟙 (j.obj y) := Category.id_comp _
  erw [hv, Q'.inverse.map_id, Category.id_comp] at h₂
  exact h₂
end Transport

universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

noncomputable def commaCoconeTargetComparison (H : D ⥤ E) :
    (commaCoconeEquivalence e d D).functor ⋙ postcomposeFunctor e d H ≅
      (whiskeringRight _ D E).obj H ⋙ (commaCoconeEquivalence e d E).functor :=
  NatIso.ofComponents (fun F => commaCoconeTargetIso F H) (by
    intro F G a
    apply Transformation.ext; funext s
    change H.map (a.app _) ≫ (𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ 𝟙 _) ≫ H.map (a.app _)
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.id_comp])

noncomputable def commaCoconeEndpointComparison (T : Data e d e' d') :
    (commaCoconeEquivalence e' d' D).functor ⋙ pullbackFunctor T ≅
      (whiskeringLeft _ _ D).obj (commaFunctor T) ⋙ (commaCoconeEquivalence e d D).functor :=
  NatIso.ofComponents (commaCoconeEndpointIso T) (by
    intro F G a
    apply Transformation.ext; funext s
    change a.app _ ≫ (commaCoconeEndpointIso T G).hom.app s = (commaCoconeEndpointIso T F).hom.app s ≫ a.app _
    rw [commaCoconeEndpoint_app, commaCoconeEndpoint_app]
    exact (a.naturality ((normalizationIso T).hom.app s)).symm)

/-- Inverse target square of the direct comma presentation, using its own packaged equivalence. -/
noncomputable def commaTargetRecovery (H : D ⥤ E) :
    postcomposeFunctor e d H ⋙ (commaCoconeEquivalence e d E).inverse ≅
      (commaCoconeEquivalence e d D).inverse ⋙ (whiskeringRight _ D E).obj H :=
  recoverySquare _ _ _ _ (commaCoconeTargetComparison H).symm

/-- Inverse endpoint square of the direct comma presentation, using its own packaged equivalence. -/
noncomputable def commaEndpointRecovery (T : Data e d e' d') :
    pullbackFunctor T ⋙ (commaCoconeEquivalence e d D).inverse ≅
      (commaCoconeEquivalence e' d' D).inverse ⋙ (whiskeringLeft _ _ D).obj (commaFunctor T) :=
  recoverySquare _ _ _ _ (commaCoconeEndpointComparison T).symm

private def whiskerInterchange {X Y : Type*} [Category* X] [Category* Y] (N : X ⥤ Y) (H : D ⥤ E) :
    (whiskeringLeft _ _ D).obj N ⋙ (whiskeringRight _ D E).obj H ⟶
      (whiskeringRight _ D E).obj H ⋙ (whiskeringLeft _ _ E).obj N where
  app G := (Functor.associator N G H).hom
  naturality := by intros; ext; simp

theorem commaCocone_inverse_target (H : D ⥤ E) (S : Cocone e d (D := D)) :
    ((coconeTargetRecovery H).hom.app S ≫ whiskerRight (commaCoconeInverseRoute.hom.app S) H) ≫
      (Functor.associator (Primitive.localizedNormalize e d) ((commaCoconeEquivalence e d D).inverse.obj S) H).hom =
    commaCoconeInverseRoute.hom.app (postcompose e d S H) ≫
      whiskerLeft (Primitive.localizedNormalize e d) ((commaTargetRecovery H).hom.app S) := by
  let u := whiskerInterchange (Primitive.localizedNormalize e d) H
  have h := recovery_route_transport (commaCoconeEquivalence e d D) (localizedCoconeEquivalence e d D)
    (commaCoconeEquivalence e d E) (localizedCoconeEquivalence e d E) _ _ _ _ _ commaCoconeRoute commaCoconeRoute
    (commaCoconeTargetComparison H) (localizedCoconeTargetComparison H) u
    (fun F => commaCocone_route_target F H) S
  simp only [commaCoconeInverseRoute, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp]
  exact h

private noncomputable def normalizationPrecomp (T : Data e d e' d') :
    (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e' d') ⋙ (whiskeringLeft _ _ D).obj (localizedFactorFunctor T) ⟶
      (whiskeringLeft _ _ D).obj (commaFunctor T) ⋙ (whiskeringLeft _ _ D).obj (Primitive.localizedNormalize e d) where
  app F := ((Functor.associator (localizedFactorFunctor T) (Primitive.localizedNormalize e' d') F).symm ≪≫
    isoWhiskerRight (localizedNormalizationIso T) F ≪≫ Functor.associator (Primitive.localizedNormalize e d) (commaFunctor T) F).hom
  naturality {F G} a := by
    apply NatTrans.ext; funext s
    change a.app _ ≫ (𝟙 _ ≫ G.map ((localizedNormalizationIso T).hom.app s) ≫ 𝟙 _) =
      (𝟙 _ ≫ F.map ((localizedNormalizationIso T).hom.app s) ≫ 𝟙 _) ≫ a.app _
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
    exact (a.naturality ((localizedNormalizationIso T).hom.app s)).symm

theorem commaCocone_inverse_endpoint (T : Data e d e' d') (S : Cocone e' d' (D := D)) :
    ((coconeEndpointRecovery T).hom.app S ≫ whiskerLeft (localizedFactorFunctor T) (commaCoconeInverseRoute.hom.app S)) ≫
      (((Functor.associator _ _ ((commaCoconeEquivalence e' d' D).inverse.obj S)).symm ≪≫
        isoWhiskerRight (localizedNormalizationIso T) _ ≪≫ Functor.associator _ _ _).hom) =
    commaCoconeInverseRoute.hom.app (pullback T S) ≫
      whiskerLeft (Primitive.localizedNormalize e d) ((commaEndpointRecovery T).hom.app S) := by
  have h := recovery_route_transport (commaCoconeEquivalence e' d' D) (localizedCoconeEquivalence e' d' D)
    (commaCoconeEquivalence e d D) (localizedCoconeEquivalence e d D) _ _ _ _ _ commaCoconeRoute commaCoconeRoute
    (commaCoconeEndpointComparison T) (localizedCoconeEndpointComparison T) (normalizationPrecomp T)
    (fun F => commaCocone_route_endpoint T F) S
  simp only [commaCoconeInverseRoute, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp]
  exact h

end ContextualComposition.Factorization.Endpoint
