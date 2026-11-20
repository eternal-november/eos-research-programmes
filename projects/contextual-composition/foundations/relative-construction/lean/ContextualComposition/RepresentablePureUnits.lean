module
public import ContextualComposition.RepresentablePureAssociativity
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureUnits
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliGeneric RepresentablePurePreframe RepresentablePureBend RepresentablePureAssociativity
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000
set_option linter.unusedSimpArgs false
section
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : (X : C) → X ⟶ F.obj X)
variable (L : ∀ {X Y : C} (f : X ⟶ F.obj Y), cmp F μ (e X) f ≅ f)
variable {X Y : C} (d : X ⟶ Y)
theorem left :
    c F μ e L (𝟙 X) d ≪≫ whiskerRightIso (λ_ d) (e Y) =
    wr F μ (λ_ (e X)) (J F e d) ≪≫ L (J F e d) := by
  apply Iso.ext
  simp only [c,pre,push,wr,J,Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Category.assoc]
  bicategory
theorem rightPre
    (n : cell F μ (𝟙 (e Y)) (λ_ (e Y)).hom ≫ (L (e Y)).hom =
      (L (J F e (𝟙 Y))).hom ≫ (λ_ (e Y)).hom) :
    c F μ e L d (𝟙 Y) ≪≫ whiskerRightIso (ρ_ d) (e Y) =
    ws F μ (J F e d) (λ_ (e Y)) ≪≫ pre F μ e L d (e Y) := by
  apply Iso.ext
  have H := natural F μ e L d (λ_ (e Y)).hom n
  rw [RepresentableKleisliGeneric.second] at H
  simp only [c,ws,J,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,
    PrelaxFunctor.map₂Iso_hom,Category.assoc]
  rw [H,triangle_assoc_comp_right]
theorem rightPreStrict [Bicategory.Strict C] :
    c F μ e L d (𝟙 Y) ≪≫ whiskerRightIso (ρ_ d) (e Y) =
    ws F μ (J F e d) (λ_ (e Y)) ≪≫ pre F μ e L d (e Y) := by
  apply rightPre
  rw [Strict.leftUnitor_eqToIso,eqToIso.hom]
  have f : J F e (𝟙 Y) = e Y := Category.id_comp _
  let t : Y ⟶ F.obj Y := J F e (𝟙 Y)
  have n (t : Y ⟶ F.obj Y) (p : t = e Y) :
      cell F μ (𝟙 (e Y)) (eqToHom p) ≫ (L (e Y)).hom = (L t).hom ≫ eqToHom p := by
    subst t
    simp only [eqToHom_refl,cell,RepresentableKleisli.horizontal,F.map₂_id,id_whiskerRight,whiskerLeft_id,Category.id_comp,Category.comp_id]
    exact Category.id_comp _
  exact n t f
variable (R : F.map (e Y) ≫ μ Y ≅ 𝟙 (F.obj Y))
def rightK (f : X ⟶ F.obj Y) : cmp F μ f (e Y) ≅ f :=
  (α_ f (F.map (e Y)) (μ Y)) ≪≫ whiskerLeftIso f R ≪≫ (ρ_ f)
theorem rightKFrame (f : Y ⟶ F.obj Y) :
    rightK F μ e R (d ≫ f) = push F μ d f (e Y) ≪≫ whiskerLeftIso d (rightK F μ e R f) := by
  apply Iso.ext
  simp only [rightK,push,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
theorem rightReady (h : L (e Y) = rightK F μ e R (e Y)) :
    pre F μ e L d (e Y) = rightK F μ e R (J F e d) := by
  rw [pre,h]
  exact (rightKFrame F μ e d R (e Y)).symm
end
end ContextualComposition.GrothendieckStep.RepresentablePureUnits
