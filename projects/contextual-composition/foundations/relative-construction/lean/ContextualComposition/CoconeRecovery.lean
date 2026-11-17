module
public import ContextualComposition.LocalizedCoconeTransport
@[expose] public section
namespace ContextualComposition
open CategoryTheory CategoryTheory.Functor
universe vA vB vA' vB' uA uB uA' uB'
variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
variable (P : A ≌ B) (Q : A' ≌ B') (H : A ⥤ A') (J : B ⥤ B')
variable (a : H ⋙ Q.functor ≅ P.functor ⋙ J)

/-- Inverse square induced by the forward comparison using the actual equivalence data. -/
def recoverySquare : J ⋙ Q.inverse ≅ P.inverse ⋙ H :=
  calc
    J ⋙ Q.inverse ≅ (𝟭 B ⋙ J) ⋙ Q.inverse := isoWhiskerRight (leftUnitor J).symm _
    _ ≅ ((P.inverse ⋙ P.functor) ⋙ J) ⋙ Q.inverse :=
      isoWhiskerRight (isoWhiskerRight P.counitIso.symm J) _
    _ ≅ (P.inverse ⋙ (P.functor ⋙ J)) ⋙ Q.inverse := isoWhiskerRight (associator _ _ _) _
    _ ≅ (P.inverse ⋙ (H ⋙ Q.functor)) ⋙ Q.inverse := isoWhiskerRight (isoWhiskerLeft _ a.symm) _
    _ ≅ ((P.inverse ⋙ H) ⋙ Q.functor) ⋙ Q.inverse := isoWhiskerRight (associator _ _ _).symm _
    _ ≅ (P.inverse ⋙ H) ⋙ (Q.functor ⋙ Q.inverse) := associator _ _ _
    _ ≅ (P.inverse ⋙ H) ⋙ 𝟭 A' := isoWhiskerLeft _ Q.unitIso.symm
    _ ≅ P.inverse ⋙ H := rightUnitor _

theorem recoverySquare_app (y : B) :
    (recoverySquare P Q H J a).hom.app y =
      Q.inverse.map (J.map (P.counitIso.inv.app y)) ≫
      Q.inverse.map (a.inv.app (P.inverse.obj y)) ≫
      Q.unitIso.inv.app (H.obj (P.inverse.obj y)) := by
  simp [recoverySquare]

set_option backward.isDefEq.respectTransparency false in
theorem recoverySquare_counit (y : B) :
    Q.functor.map ((recoverySquare P Q H J a).hom.app y) ≫ a.hom.app (P.inverse.obj y) ≫
      J.map (P.counitIso.hom.app y) = Q.counitIso.hom.app (J.obj y) := by
  rw [recoverySquare_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Q.counit_app_functor]
  erw [Q.counitIso.hom.naturality_assoc (a.inv.app (P.inverse.obj y))]
  simp only [Functor.id_map, Iso.inv_hom_id_app_assoc]
  erw [Q.counitIso.hom.naturality_assoc (J.map (P.counitIso.inv.app y))]
  simp

theorem recoverySquare_unit (x : A) :
    Q.unitIso.hom.app (H.obj x) ≫ Q.inverse.map (a.hom.app x) ≫
      (recoverySquare P Q H J a).hom.app (P.functor.obj x) = H.map (P.unitIso.hom.app x) :=
  unit_square_of_counit P Q H J a _ (recoverySquare_counit P Q H J a) x
/-- Counit compatibility characterizes the entire inverse transformation. -/
theorem recoverySquare_unique (b : J ⋙ Q.inverse ⟶ P.inverse ⋙ H)
    (hb : ∀ y, Q.functor.map (b.app y) ≫ a.hom.app (P.inverse.obj y) ≫
      J.map (P.counitIso.hom.app y) = Q.counitIso.hom.app (J.obj y)) :
    b = (recoverySquare P Q H J a).hom := by
  apply NatTrans.ext; funext y
  apply Q.functor.map_injective
  apply (cancel_mono (a.hom.app (P.inverse.obj y) ≫ J.map (P.counitIso.hom.app y))).mp
  exact (hb y).trans (recoverySquare_counit P Q H J a y).symm
end ContextualComposition

namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

section Endpoint
variable (T : Data e d e' d')

/-- Recovery using the inverse of the actual composite equivalence commutes with endpoint pullback. -/
noncomputable def coconeEndpointRecovery : (pullbackFunctor T (D := D)) ⋙ (localizedCoconeEquivalence e d D).inverse ≅ (localizedCoconeEquivalence e' d' D).inverse ⋙ ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)) :=
  recoverySquare (localizedCoconeEquivalence e' d' D) (localizedCoconeEquivalence e d D) ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)) (pullbackFunctor T (D := D)) ((localizedCoconeEndpointComparison T (D := D))).symm

theorem coconeEndpointRecovery_counit (S : Cocone e' d' (D := D)) :
    (localizedCoconeEquivalence e d D).functor.map ((coconeEndpointRecovery T).hom.app S) ≫ ((localizedCoconeEndpointComparison T (D := D))).inv.app ((localizedCoconeEquivalence e' d' D).inverse.obj S) ≫
      (pullbackFunctor T (D := D)).map ((localizedCoconeEquivalence e' d' D).counitIso.hom.app S) = (localizedCoconeEquivalence e d D).counitIso.hom.app ((pullbackFunctor T (D := D)).obj S) :=
  recoverySquare_counit (localizedCoconeEquivalence e' d' D) (localizedCoconeEquivalence e d D) ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)) (pullbackFunctor T (D := D)) ((localizedCoconeEndpointComparison T (D := D))).symm S

theorem coconeEndpointRecovery_unit (G : (Primitive.generators e' d').Localization ⥤ D) :
    (localizedCoconeEquivalence e d D).unitIso.hom.app (((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)).obj G) ≫ (localizedCoconeEquivalence e d D).inverse.map (((localizedCoconeEndpointComparison T (D := D))).inv.app G) ≫
      (coconeEndpointRecovery T).hom.app ((localizedCoconeEquivalence e' d' D).functor.obj G) = ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)).map ((localizedCoconeEquivalence e' d' D).unitIso.hom.app G) :=
  recoverySquare_unit (localizedCoconeEquivalence e' d' D) (localizedCoconeEquivalence e d D) ((whiskeringLeft _ _ D).obj (localizedFactorFunctor T)) (pullbackFunctor T (D := D)) ((localizedCoconeEndpointComparison T (D := D))).symm G
end Endpoint

section Target
variable (H : D ⥤ E)
/-- Assemble the already proved target naturality on arbitrary functor transformations. -/
noncomputable def localizedCoconeTargetComparison :
    (localizedCoconeEquivalence e d D).functor ⋙ (postcomposeFunctor e d H) ≅ ((whiskeringRight _ D E).obj H) ⋙ (localizedCoconeEquivalence e d E).functor :=
  NatIso.ofComponents (fun G => localizedCoconeTargetIso G H)
    (fun a => localizedCocone_target_naturality a H)

noncomputable def coconeTargetRecovery : (postcomposeFunctor e d H) ⋙ (localizedCoconeEquivalence e d E).inverse ≅ (localizedCoconeEquivalence e d D).inverse ⋙ ((whiskeringRight _ D E).obj H) :=
  recoverySquare (localizedCoconeEquivalence e d D) (localizedCoconeEquivalence e d E) ((whiskeringRight _ D E).obj H) (postcomposeFunctor e d H) (localizedCoconeTargetComparison (e := e) (d := d) H).symm

theorem coconeTargetRecovery_counit (S : Cocone e d (D := D)) :
    (localizedCoconeEquivalence e d E).functor.map ((coconeTargetRecovery H).hom.app S) ≫ (localizedCoconeTargetComparison (e := e) (d := d) H).inv.app ((localizedCoconeEquivalence e d D).inverse.obj S) ≫
      (postcomposeFunctor e d H).map ((localizedCoconeEquivalence e d D).counitIso.hom.app S) = (localizedCoconeEquivalence e d E).counitIso.hom.app ((postcomposeFunctor e d H).obj S) :=
  recoverySquare_counit (localizedCoconeEquivalence e d D) (localizedCoconeEquivalence e d E) ((whiskeringRight _ D E).obj H) (postcomposeFunctor e d H) (localizedCoconeTargetComparison (e := e) (d := d) H).symm S

theorem coconeTargetRecovery_unit (G : (Primitive.generators e d).Localization ⥤ D) :
    (localizedCoconeEquivalence e d E).unitIso.hom.app (((whiskeringRight _ D E).obj H).obj G) ≫ (localizedCoconeEquivalence e d E).inverse.map ((localizedCoconeTargetComparison (e := e) (d := d) H).inv.app G) ≫
      (coconeTargetRecovery H).hom.app ((localizedCoconeEquivalence e d D).functor.obj G) = ((whiskeringRight _ D E).obj H).map ((localizedCoconeEquivalence e d D).unitIso.hom.app G) :=
  recoverySquare_unit (localizedCoconeEquivalence e d D) (localizedCoconeEquivalence e d E) ((whiskeringRight _ D E).obj H) (postcomposeFunctor e d H) (localizedCoconeTargetComparison (e := e) (d := d) H).symm G
end Target
end ContextualComposition.Factorization.Endpoint
