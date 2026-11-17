module
public import ContextualComposition.NormalizationCoherence
@[expose] public section
namespace ContextualComposition
open CategoryTheory
universe vA vB vA' vB' uA uB uA' uB'
variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
set_option backward.isDefEq.respectTransparency false in
/-- A counit-compatible square of equivalences respects their actual units. -/
theorem unit_square_of_counit (E : A ≌ B) (E' : A' ≌ B')
    (H : A ⥤ A') (J : B ⥤ B')
    (a : H ⋙ E'.functor ≅ E.functor ⋙ J)
    (b : J ⋙ E'.inverse ≅ E.inverse ⋙ H)
    (hc : ∀ y, E'.functor.map (b.hom.app y) ≫ a.hom.app (E.inverse.obj y) ≫
      J.map (E.counitIso.hom.app y) = E'.counitIso.hom.app (J.obj y)) (x : A) :
    E'.unitIso.hom.app (H.obj x) ≫ E'.inverse.map (a.hom.app x) ≫
      b.hom.app (E.functor.obj x) = H.map (E.unitIso.hom.app x) := by
  apply E'.functor.map_injective
  apply (cancel_mono (a.hom.app (E.inverse.obj (E.functor.obj x)) ≫
    J.map (E.counitIso.hom.app (E.functor.obj x)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  erw [E'.counitIso.hom.naturality (a.hom.app x)]
  simp only [Functor.comp_obj, Functor.id_map]
  erw [← Category.assoc, E'.functor_unitIso_comp, Category.id_comp]
  erw [← Category.assoc, a.hom.naturality (E.unitIso.hom.app x)]
  simp only [Functor.comp_map, Category.assoc]
  erw [← J.map_comp, E.functor_unitIso_comp, J.map_id, Category.comp_id]
  rfl
end ContextualComposition

namespace ContextualComposition.Factorization.Endpoint
open CategoryTheory CategoryTheory.Functor
universe vK vL vK' vL' vC uK uL uK' uL' uC
variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'} {C : Type uC}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vK'} K'] [Category.{vL'} L'] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- The packaged counit is the original factorization comparison followed by the section law. -/
theorem packaged_counit_app (s : Comma e d) :
    (Primitive.localizationEquivalence e d).counitIso.hom.app s =
      (normalizationFac e d).hom.app ((sectionFunctor e d).obj s) ≫
        (sectionIso e d).hom.app s := by
  dsimp [Primitive.localizationEquivalence, CategoryTheory.Equivalence.mk, normalizationFac, Primitive.localizedSection]
  simp

/-- The source section and normalization squares respect the source section law. -/
theorem source_counit_compatibility (T : Data e d e' d') (s : Comma e d) :
    (normalize e' d').map ((sectionComparison T).app s) ≫
      (normalizationIso T).hom.app ((sectionFunctor e d).obj s) ≫
      (commaFunctor T).map ((sectionIso e d).hom.app s) =
    (sectionIso e' d').hom.app ((commaFunctor T).obj s) := by
  apply Comma.hom_ext
  · change 𝟙 _ ≫ 𝟙 _ ≫ T.input.map (𝟙 _) = 𝟙 _
    simp
  · change 𝟙 _ ≫ 𝟙 _ ≫ T.output.map (𝟙 _) = 𝟙 _
    simp

set_option backward.isDefEq.respectTransparency false in
theorem packaged_counit_compatibility (T : Data e d e' d') (s : Comma e d) :
    (Primitive.localizedNormalize e' d').map ((sectionTransportIso T).hom.app s) ≫
      (localizedNormalizationIso T).hom.app ((Primitive.localizedSection e d).obj s) ≫
      (commaFunctor T).map ((Primitive.localizationEquivalence e d).counitIso.hom.app s) =
    (Primitive.localizationEquivalence e' d').counitIso.hom.app ((commaFunctor T).obj s) := by
  rw [sectionTransport_app, packaged_counit_app, packaged_counit_app]
  change _ ≫ (localizedNormalizationIso T).hom.app
    ((Primitive.generators e d).Q.obj ((sectionFunctor e d).obj s)) ≫ _ = _
  rw [localizedNormalization_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [((Primitive.localizedNormalize e' d').mapIso
    ((chosenLift T).comparison.app ((sectionFunctor e d).obj s))).inv_hom_id_assoc]
  erw [(normalizationFac e' d').hom.naturality_assoc ((sectionComparison T).app s)]
  dsimp only [normalizationFac, Primitive.localizedNormalize, Primitive.localizedSection, Functor.comp_map, Functor.comp_obj]
  erw [((commaFunctor T).mapIso
    ((normalizationFac e d).app ((sectionFunctor e d).obj s))).inv_hom_id_assoc]
  erw [source_counit_compatibility]

/-- Compatibility with the actual adjointified unit of the existing packaged equivalence. -/
theorem packaged_unit_compatibility (T : Data e d e' d')
    (s : (Primitive.generators e d).Localization) :
    (Primitive.localizationEquivalence e' d').unitIso.hom.app ((localizedFactorFunctor T).obj s) ≫
      (Primitive.localizedSection e' d').map ((localizedNormalizationIso T).hom.app s) ≫
      (sectionTransportIso T).hom.app ((Primitive.localizedNormalize e d).obj s) =
    (localizedFactorFunctor T).map ((Primitive.localizationEquivalence e d).unitIso.hom.app s) := by
  exact ContextualComposition.unit_square_of_counit
    (Primitive.localizationEquivalence e d) (Primitive.localizationEquivalence e' d')
    (localizedFactorFunctor T) (commaFunctor T) (localizedNormalizationIso T)
    (sectionTransportIso T) (packaged_counit_compatibility T) s

end ContextualComposition.Factorization.Endpoint
