module
public import ContextualComposition.RecoveryTargetLaws

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
open GrothendieckStep GrothendieckStep.FibreValue
universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
variable {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

private def prePost {X Y : Type*} [Category* X] [Category* Y] (T : X ⥤ Y) (H : D ⥤ E) :
    (whiskeringLeft X Y D).obj T ⋙ (whiskeringRight X D E).obj H ⟶
      (whiskeringRight Y D E).obj H ⋙ (whiskeringLeft X Y E).obj T where
  app G := (Functor.associator T G H).hom
  naturality := by intros; ext; simp

private theorem switchSides {B : Type*} [Category* B] {x y z w : B}
    (i : x ≅ y) (j : z ≅ w) (f : y ⟶ w) (g : x ⟶ z) (h : i.hom ≫ f = g ≫ j.hom) :
    i.inv ≫ g = f ≫ j.inv := by
  apply (cancel_epi i.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint pullback and target postcomposition satisfy interchange on the actual inverse recovery. -/
theorem coconeRecovery_interchange (T : Data e d e' d') (H : D ⥤ E) (S : Cocone e' d' (D := D)) :
    ((coconeTargetRecovery H).hom.app (pullback T S) ≫
      whiskerRight ((coconeEndpointRecovery T).hom.app S) H) ≫
      (Functor.associator (localizedFactorFunctor T) ((localizedCoconeEquivalence e' d' D).inverse.obj S) H).hom =
    (localizedCoconeEquivalence e d E).inverse.map (pullbackPostcomposeIso T S H).hom ≫
      (coconeEndpointRecovery T).hom.app (postcompose e' d' S H) ≫
      whiskerLeft (localizedFactorFunctor T) ((coconeTargetRecovery H).hom.app S) := by
  let P := localizedCoconeEquivalence e' d' D
  let Q := localizedCoconeEquivalence e d E
  let b := localizedCoconeEndpointComparison T (D := D)
  let l := localizedCoconeTargetComparison (e := e) (d := d) H
  let r := localizedCoconeTargetComparison (e := e') (d := d') H
  let t := localizedCoconeEndpointComparison T (D := E)
  let δ : P.functor ⋙ (pullbackFunctor T ⋙ postcomposeFunctor e d H) ≅
      ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T) ⋙ (whiskeringRight _ D E).obj H) ⋙ Q.functor :=
    (Functor.associator P.functor (pullbackFunctor T) (postcomposeFunctor e d H)).symm ≪≫
      isoWhiskerRight b (postcomposeFunctor e d H) ≪≫
      Functor.associator _ (localizedCoconeEquivalence e d D).functor _ ≪≫
      isoWhiskerLeft ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)) l ≪≫
      (Functor.associator _ _ Q.functor).symm
  let u := prePost (localizedFactorFunctor T) H
  let v := (pullbackTargetComparison T H).hom
  have first : Paste.CompLaw δ.symm l.symm b.symm (𝟙 _) (𝟙 _) := by
    intro G
    simp [δ]
  have second : Paste.CompLaw δ.symm t.symm r.symm u v := by
    intro G
    let i := (postcomposeFunctor e d H).mapIso (localizedCoconeEndpointIso T G) ≪≫
      localizedCoconeTargetIso (localizedFactorFunctor T ⋙ G) H
    let j := (pullbackFunctor T).mapIso (localizedCoconeTargetIso G H) ≪≫
      localizedCoconeEndpointIso T (G ⋙ H)
    let f := Q.functor.map (Functor.associator (localizedFactorFunctor T) G H).hom
    let g := (pullbackPostcomposeIso T (localizedCocone G) H).hom
    have comm : i.hom ≫ f = g ≫ j.hom := by
      change ((postcomposeMap e d H (localizedCoconeEndpointIso T G).hom) ≫
        (localizedCoconeTargetIso (localizedFactorFunctor T ⋙ G) H).hom) ≫ _ = _
      rw [Category.assoc]
      exact localizedCocone_endpoint_target T G H
    have h := switchSides i j f g comm
    change δ.inv.app G ≫ g =
      f ≫ (localizedCoconeEndpointIso T (G ⋙ H)).inv ≫ (pullbackFunctor T).map (localizedCoconeTargetIso G H).inv
    have component : δ.inv.app G = i.inv := by
      simp [δ, i, l, b, localizedCoconeTargetComparison, localizedCoconeEndpointComparison]
    rw [component]
    exact h
  have h₁ := MateLaws.comp Q (localizedCoconeEquivalence e d D) P δ l b (𝟙 _) (𝟙 _) first S
  have h₂ := MateLaws.comp Q (localizedCoconeEquivalence e' d' E) P δ t r u v second S
  simp only [← recovery_eq_mate, Iso.symm_hom, Iso.symm_inv, NatTrans.id_app, Functor.map_id,
    Category.id_comp] at h₁ h₂
  have firstPath := (Category.comp_id ((recoverySquare P Q _ _ δ.symm).hom.app S)).symm.trans h₁
  rw [firstPath] at h₂
  exact h₂

end ContextualComposition.Factorization.Endpoint
