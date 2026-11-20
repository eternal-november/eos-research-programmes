module
public import ContextualComposition.RepresentablePentagonSeam
public import ContextualComposition.RepresentableMultiplicationPaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonShort
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliGeneric RepresentablePentagonWord RepresentableKleisliPentagonPaths
open RepresentablePentagonSeam
open AmbientHorizontalDiagrams RepresentableKleisliConstraints RepresentableStrictFold RepresentableMultiplicationPaste
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
section
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {U V X Y Z : C}
theorem comp₂ {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    F.map (F.map (f ≫ g)) = F.map (F.map f) ≫ F.map (F.map g) := by rw [F.map_comp,F.map_comp]
variable (di : ∀ {x y z : C} (p : x ⟶ y) (q : y ⟶ z),
    D (p ≫ q) = paste (comp₂ F p q) (F.map_comp p q).symm (D p) (D q))
variable (f : U ⟶ F.obj V) (g : V ⟶ F.obj X) (h : X ⟶ F.obj Y) (i : Y ⟶ F.obj Z)
include di in
theorem branch :
    D (cmp F μ h i) =
    paste (comp₂ F (h ≫ F.map i) (μ Z)) (F.map_comp (h ≫ F.map i) (μ Z)).symm
      (paste (comp₂ F h (F.map i)) (F.map_comp h (F.map i)).symm (D h) (D (F.map i))) (D (μ Z)) :=
  (di (h ≫ F.map i) (μ Z)).trans (congrArg (fun j => paste (comp₂ F (h ≫ F.map i) (μ Z))
    (F.map_comp (h ≫ F.map i) (μ Z)).symm j (D (μ Z))) (di h (F.map i)))
include di in
theorem normalize :
    originalShort F μ D a f g h i = wordShort F μ D a f g h i := by
  apply Iso.ext
  simp only [originalShort,bend,branch F μ D di h i,
    wordShort,bridge,short,expand,unfoldThree,moveTail,moveHead,L,paste,
    Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_hom,whiskerLeftIso_inv,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  simp only [F.mapComp_eq_eqToIso,Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,comp_whiskerLeft,Bicategory.whiskerRight_comp,whisker_assoc,
    whiskerLeft_eqToHom,eqToHom_whiskerRight,Category.assoc,eqToHom_trans,eqToHom_trans_assoc,eqToHom_refl,
    Category.id_comp,Category.comp_id]
  have H : F.map (F.map (RepresentableKleisliGeneric.cmp F μ h i)) =
      (F.map (F.map h) ≫ F.map (F.map (F.map i))) ≫ F.map (F.map (μ Z)) := by
    simp only [RepresentableKleisliGeneric.cmp,F.map_comp]
  rw [prefixCast₂_assoc f (F.map g) (comp₂ F h (F.map i)),prefixCast₂ f (F.map g) H]
  simp only [RepresentableKleisliGeneric.cmp,Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,
    whiskerLeft_eqToHom,eqToHom_whiskerRight,Bicategory.whiskerLeft_comp,comp_whiskerLeft,
    Category.assoc,eqToHom_trans,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp,Category.comp_id]
end
end ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonShort
