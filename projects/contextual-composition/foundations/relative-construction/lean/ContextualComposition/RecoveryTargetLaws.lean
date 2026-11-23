module
public import ContextualComposition.RecoveryModification
public import ContextualComposition.MateLaws

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
open GrothendieckStep GrothendieckStep.FibreValue

private theorem recovery_eq_mate {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    (P : A ≌ B) (Q : A' ≌ B') {H : A ⥤ A'} {J : B ⥤ B'}
    (a : P.functor ⋙ J ≅ H ⋙ Q.functor) :
    (recoverySquare P Q H J a.symm).symm = SumChange.inverseSquare P Q a := by
  apply Iso.ext
  apply NatTrans.ext
  funext y
  apply MateLaws.decode_inj Q
  rw [MateLaws.mate_fac]
  change Q.functor.map ((recoverySquare P Q H J a.symm).inv.app y) ≫
    Q.counitIso.hom.app (J.obj y) = _
  rw [← recoverySquare_counit P Q H J a.symm y]
  simp only [← Q.functor.map_comp_assoc, Iso.inv_hom_id_app, Q.functor.map_id, Category.id_comp,
    Iso.symm_hom]

private def postUnit (X D : Type*) [Category* X] [Category* D] :
    (whiskeringRight X D D).obj (𝟭 D) ⟶ 𝟭 _ where
  app G := (Functor.rightUnitor G).hom
  naturality := by intros; ext; simp

private def postComp (X : Type*) [Category* X] {D E F : Type*}
    [Category* D] [Category* E] [Category* F] (H : D ⥤ E) (J : E ⥤ F) :
    (whiskeringRight X D F).obj (H ⋙ J) ⟶
      (whiskeringRight X D E).obj H ⋙ (whiskeringRight X E F).obj J where
  app G := (Functor.associator G H J).inv
  naturality := by intros; ext; simp

universe vK vL vC vD vE vF uK uL uC uD uE uF
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C]
variable [Category.{vD} D] [Category.{vE} E] [Category.{vF} F] {e : K ⥤ C} {d : L ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the packaged equivalence preserves identity target change with its specified unitor. -/
theorem coconeTargetRecovery_identity (S : Cocone e d (D := D)) :
    (coconeTargetRecovery (𝟭 D)).hom.app S ≫
      (Functor.rightUnitor ((localizedCoconeEquivalence e d D).inverse.obj S)).hom =
    (localizedCoconeEquivalence e d D).inverse.map (postcomposeIdIso e d S).hom := by
  let P := localizedCoconeEquivalence e d D
  let a := localizedCoconeTargetComparison (e := e) (d := d) (𝟭 D)
  let u := postUnit (Primitive.generators e d).Localization D
  let v := (postcomposeIdentity e d (D := D)).hom
  have fwd : Paste.UnitLaw a.symm u v := by
    intro G
    change (localizedCoconeTargetIso G (𝟭 D)).inv ≫
      (postcomposeIdIso e d (localizedCocone G)).hom = _
    rw [← localizedCocone_target_identity G, Iso.inv_hom_id_assoc]
    rfl
  have h := MateLaws.unit P a u v fwd S
  rw [← recovery_eq_mate] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Successive target changes on the actual inverse recovery use the cocone compositor and the functor associator. -/
theorem coconeTargetRecovery_composition (S : Cocone e d (D := D)) (H : D ⥤ E) (J : E ⥤ F) :
    (coconeTargetRecovery (H ⋙ J)).hom.app S ≫
      (Functor.associator ((localizedCoconeEquivalence e d D).inverse.obj S) H J).inv =
    (localizedCoconeEquivalence e d F).inverse.map (postcomposeCompIso e d S H J).inv ≫
      (coconeTargetRecovery J).hom.app (postcompose e d S H) ≫
      whiskerRight ((coconeTargetRecovery H).hom.app S) J := by
  let a := localizedCoconeTargetComparison (e := e) (d := d) J
  let b := localizedCoconeTargetComparison (e := e) (d := d) H
  let c := localizedCoconeTargetComparison (e := e) (d := d) (H ⋙ J)
  let u := postComp (Primitive.generators e d).Localization H J
  let v := (postcomposeComposition e d H J).inv
  have fwd : Paste.CompLaw c.symm a.symm b.symm u v := by
    intro G
    have eq : postcomposeCompIso e d (localizedCocone G) H J ≪≫ localizedCoconeTargetIso G (H ⋙ J) =
        (postcomposeFunctor e d J).mapIso (localizedCoconeTargetIso G H) ≪≫
        localizedCoconeTargetIso (G ⋙ H) J ≪≫
        (localizedCoconeEquivalence e d F).functor.mapIso (Functor.associator G H J) :=
      Iso.ext (localizedCocone_target_composition G H J)
    change (localizedCoconeTargetIso G (H ⋙ J)).inv ≫ (postcomposeCompIso e d (localizedCocone G) H J).inv =
      (localizedCoconeEquivalence e d F).functor.map (Functor.associator G H J).inv ≫
      (localizedCoconeTargetIso (G ⋙ H) J).inv ≫ (postcomposeFunctor e d J).map (localizedCoconeTargetIso G H).inv
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using congrArg Iso.inv eq
  have h := MateLaws.comp (localizedCoconeEquivalence e d F) (localizedCoconeEquivalence e d E)
    (localizedCoconeEquivalence e d D) c a b u v fwd S
  simp only [← recovery_eq_mate] at h
  exact h

end ContextualComposition.Factorization.Endpoint
