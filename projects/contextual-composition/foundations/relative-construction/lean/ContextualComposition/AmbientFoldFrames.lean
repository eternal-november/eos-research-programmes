module
public import ContextualComposition.AmbientNestedGrade
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFoldFrames
open CategoryTheory CategoryTheory.Functor Opposite CategoryTheory.Bicategory
open AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
universe u
variable {C : Type u} [Bicategory C] (F : StrictPseudofunctor C C)
variable {x y z w : C} {p : x ⟶ y} {q : y ⟶ z} {t : x ⟶ w} {v : w ⟶ z}
theorem mapHom (h : p ≫ q ≅ t ≫ v) : (foldMap F h).hom =
    eqToHom (F.map_comp p q).symm ≫ F.map₂ h.hom ≫ eqToHom (F.map_comp t v) := by
  simp only [foldMap,Iso.trans_hom,Iso.symm_hom,F.mapComp_eq_eqToIso,eqToIso.inv,eqToIso.hom]; rfl
theorem mapInv (h : p ≫ q ≅ t ≫ v) : (foldMap F h).inv =
    eqToHom (F.map_comp t v).symm ≫ F.map₂ h.inv ≫ eqToHom (F.map_comp p q) := by
  simp [foldMap,F.mapComp_eq_eqToIso]
theorem unitHom {q : y ⟶ x} (h : p ≫ q ≅ 𝟙 x) : (foldUnit F h).hom =
    eqToHom (F.map_comp p q).symm ≫ F.map₂ h.hom ≫ eqToHom (F.map_id x) := by
  simp only [foldUnit,Iso.trans_hom,Iso.symm_hom,F.mapComp_eq_eqToIso,F.mapId_eq_eqToIso,eqToIso.inv,eqToIso.hom]; rfl
end ContextualComposition.GrothendieckStep.AmbientFoldFrames
