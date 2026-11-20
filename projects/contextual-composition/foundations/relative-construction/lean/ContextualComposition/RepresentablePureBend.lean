module
public import ContextualComposition.RepresentablePurePreframe
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureBend
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliGeneric RepresentablePurePreframe
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option linter.unusedSimpArgs false
section Generic
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : (X : C) → X ⟶ F.obj X)
variable (L : ∀ {X Y : C} (f : X ⟶ F.obj Y), cmp F μ (e X) f ≅ f)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {X Y Z W : C}
def pre (d : X ⟶ Y) (g : Y ⟶ F.obj Z) :
    cmp F μ (d ≫ e Y) g ≅ d ≫ g :=
  push F μ d (e Y) g ≪≫ whiskerLeftIso d (L g)
theorem natural (d : X ⟶ Y) {g g' : Y ⟶ F.obj Z} (t : g ⟶ g')
    (n : cell F μ (𝟙 (e Y)) t ≫ (L g').hom = (L g).hom ≫ t) :
    cell F μ (𝟙 (d ≫ e Y)) t ≫ (pre F μ e L d g').hom = (pre F μ e L d g).hom ≫ d ◁ t := by
  rw [RepresentableKleisliGeneric.second] at n ⊢
  simp only [pre,Iso.trans_hom,whiskerLeftIso_hom,Category.assoc]
  rw [← Category.assoc (((d ≫ e Y) ◁ F.map₂ t) ▷ μ Z),natural₂ F μ d (e Y) g t,Category.assoc]
  have Q := congrArg (fun i => d ◁ i) n
  simp only [Bicategory.whiskerLeft_comp] at Q
  rw [Q]
theorem right (d : X ⟶ Y) (g : Y ⟶ F.obj Z) (h : Z ⟶ F.obj W)
    (l : bend F μ D a (e Y) g h ≪≫ L (cmp F μ g h) =
      whiskerRightIso (whiskerRightIso (L g) (F.map h)) (μ W)) :
    bend F μ D a (d ≫ e Y) g h ≪≫ pre F μ e L d (cmp F μ g h) =
    whiskerRightIso (whiskerRightIso (pre F μ e L d g) (F.map h)) (μ W) ≪≫ push F μ d g h := by
  unfold pre
  rw [← Iso.trans_assoc,linear F μ D a d (e Y) g h]
  apply Iso.ext
  have hL := congrArg Iso.hom l
  simp only [Iso.trans_hom,whiskerRightIso_hom] at hL
  simp only [Iso.trans_hom,whiskerRightIso_hom,whiskerLeftIso_hom,Category.assoc,
    comp_whiskerRight,Bicategory.whiskerLeft_comp]
  have Q := congrArg (fun i => d ◁ i) hL
  simp only [Bicategory.whiskerLeft_comp] at Q
  rw [Q,natural₁ F μ d (cmp F μ (e Y) g) h (L g).hom]
theorem preCompose (d : X ⟶ Y) (b : Y ⟶ Z) (g : Z ⟶ F.obj W) :
    whiskerRightIso (whiskerRightIso (α_ d b (e Z)) (F.map g)) (μ W) ≪≫
      push F μ d (b ≫ e Z) g ≪≫ whiskerLeftIso d (pre F μ e L b g) ≪≫ (α_ d b g).symm =
    pre F μ e L (d ≫ b) g := by
  apply Iso.ext
  simp only [pre,push,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,
    Bicategory.whiskerLeft_comp,comp_whiskerRight,Category.assoc]
  bicategory
end Generic
end ContextualComposition.GrothendieckStep.RepresentablePureBend
