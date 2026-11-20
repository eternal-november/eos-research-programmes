module
public import ContextualComposition.RepresentablePentagonSeam
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonLong
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliGeneric RepresentablePentagonWord RepresentableKleisliPentagonPaths
open RepresentablePentagonSeam
open AmbientHorizontalDiagrams RepresentableKleisliConstraints RepresentableStrictFold
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {U V X Y Z : C}
variable (f : U ⟶ F.obj V) (g : V ⟶ F.obj X) (h : X ⟶ F.obj Y) (i : Y ⟶ F.obj Z)
theorem normalize :
    originalLong F μ D a f g h i = wordLong F μ D a f g h i := by
  apply Iso.ext
  simp only [originalLong,wordLong,bridge,long,bend,expand,unfoldThree,moveTail,moveHead,L,foldMap,
    Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_hom,whiskerLeftIso_inv,
    PrelaxFunctor.map₂Iso_hom,PrelaxFunctor.map₂Iso_inv,PrelaxFunctor.map₂_comp,
    Pseudofunctor.map₂_whisker_left,Pseudofunctor.map₂_whisker_right,Pseudofunctor.map₂_associator,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc,
    hom_inv_whiskerRight_assoc,inv_hom_whiskerRight_assoc,Iso.inv_hom_id_assoc]
  simp only [F.mapComp_eq_eqToIso,Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,PrelaxFunctor.map₂_eqToHom,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,comp_whiskerLeft,Bicategory.whiskerRight_comp,whisker_assoc,
    whiskerLeft_eqToHom,eqToHom_whiskerRight,Category.assoc,eqToHom_trans,eqToHom_trans_assoc,eqToHom_refl,
    Category.id_comp,Category.comp_id]
  rw [prefixCast_assoc f (fold F μ g h),prefixCast_assoc f (fold F μ g h),
    prefixCast_assoc f (F.map_comp g (F.map h)),
    prefixCast f ((F.map_comp (g ≫ F.map h) (F.map (F.map i))).trans
      (congrArg (· ≫ F.map (F.map (F.map i))) (F.map_comp g (F.map h))))]
  simp only [Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,whiskerLeft_eqToHom,eqToHom_whiskerRight,Bicategory.whiskerLeft_comp,comp_whiskerLeft,Category.assoc,eqToHom_trans,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp,Category.comp_id]
end ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonLong
