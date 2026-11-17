module
public import ContextualComposition.CoconeRecovery
@[expose] public section
namespace ContextualComposition
open CategoryTheory CategoryTheory.Functor
universe vA vB vA' vB' uA uB uA' uB'
variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
variable (P : A ≌ B) (Q : A' ≌ B') {H I : A ⥤ A'} {J K : B ⥤ B'}
set_option backward.isDefEq.respectTransparency false in
/-- A compatible pair of possibly noninvertible side transformations acts on the
actual inverse recovery squares, in the original (covariant) direction. -/
theorem recoverySquare_modification
    (a : H ⋙ Q.functor ≅ P.functor ⋙ J) (b : I ⋙ Q.functor ≅ P.functor ⋙ K)
    (h : H ⟶ I) (j : J ⟶ K)
    (w : ∀ x, j.app (P.functor.obj x) ≫ b.inv.app x =
      a.inv.app x ≫ Q.functor.map (h.app x)) (y : B) :
    Q.inverse.map (j.app y) ≫ (recoverySquare P Q I K b).hom.app y =
      (recoverySquare P Q H J a).hom.app y ≫ h.app (P.inverse.obj y) := by
  rw [recoverySquare_app, recoverySquare_app]
  simp only [Category.assoc]
  rw [← Q.inverse.map_comp_assoc, ← j.naturality, Q.inverse.map_comp_assoc]
  congr 1
  erw [← Q.inverse.map_comp_assoc, w (P.inverse.obj y), Q.inverse.map_comp_assoc]
  erw [Q.unitIso.inv.naturality (h.app (P.inverse.obj y))]
  rfl

/-- Pasting two compatible side transformations vertically uses the same intermediate
recovery square. No invertibility of the changes of sides is necessary. -/
theorem recoverySquare_vertical {L : A ⥤ A'} {M : B ⥤ B'}
    (a : H ⋙ Q.functor ≅ P.functor ⋙ J) (b : I ⋙ Q.functor ≅ P.functor ⋙ K)
    (c : L ⋙ Q.functor ≅ P.functor ⋙ M)
    (h : H ⟶ I) (j : J ⟶ K) (k : I ⟶ L) (m : K ⟶ M)
    (w : ∀ x, j.app (P.functor.obj x) ≫ b.inv.app x = a.inv.app x ≫ Q.functor.map (h.app x))
    (v : ∀ x, m.app (P.functor.obj x) ≫ c.inv.app x = b.inv.app x ≫ Q.functor.map (k.app x))
    (y : B) :
    Q.inverse.map ((j ≫ m).app y) ≫ (recoverySquare P Q L M c).hom.app y =
      (recoverySquare P Q H J a).hom.app y ≫ (h ≫ k).app (P.inverse.obj y) := by
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [recoverySquare_modification P Q b c k m v, ← Category.assoc,
    recoverySquare_modification P Q a b h j w, Category.assoc]

end ContextualComposition

namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor Source
universe vK vL vK' vL' vC vD vE uK uL uK' uL' uC uD uE
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable {D : Type uD} {E : Type uE}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L']
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

/-- The previously specified choice isomorphisms are natural in arbitrary cocone maps. -/
noncomputable def pullbackChoiceComparison {T U : Data e d e' d'} (a : ChoiceIso T U) :
    pullbackFunctor T (D := D) ≅ pullbackFunctor U :=
  NatIso.ofComponents (pullbackChoiceIso a) (by
    intro S V f
    apply Transformation.ext; funext s
    exact ((extensionTransformation e' d' f).naturality (a.factorIso.hom.app s)).symm)

theorem coconeEndpointRecovery_choice {T U : Data e d e' d'} (a : ChoiceIso T U)
    (S : Cocone e' d' (D := D)) :
    (localizedCoconeEquivalence e d D).inverse.map ((pullbackChoiceIso a S).hom) ≫
      (coconeEndpointRecovery U).hom.app S =
    (coconeEndpointRecovery T).hom.app S ≫ whiskerRight (localizedChoiceIso a).hom
      ((localizedCoconeEquivalence e' d' D).inverse.obj S) :=
  recoverySquare_modification (localizedCoconeEquivalence e' d' D)
    (localizedCoconeEquivalence e d D) (localizedCoconeEndpointComparison T).symm
    (localizedCoconeEndpointComparison U).symm
    ((whiskeringLeft _ _ D).map (localizedChoiceIso a).hom)
    (pullbackChoiceComparison a).hom (localizedCocone_endpoint_choice a) S

theorem coconeTargetRecovery_transformation {H J : D ⥤ E} (τ : H ⟶ J)
    (S : Cocone e d (D := D)) :
    (localizedCoconeEquivalence e d E).inverse.map (targetTransformation e d τ S) ≫
      (coconeTargetRecovery J).hom.app S =
    (coconeTargetRecovery H).hom.app S ≫
      whiskerLeft ((localizedCoconeEquivalence e d D).inverse.obj S) τ :=
  recoverySquare_modification (localizedCoconeEquivalence e d D) (localizedCoconeEquivalence e d E)
    (localizedCoconeTargetComparison H).symm (localizedCoconeTargetComparison J).symm
    ((whiskeringRight _ D E).map τ) (targetNaturalTransformation e d τ)
    (fun G => localizedCocone_target_transformation G τ) S
end ContextualComposition.Factorization.Endpoint
