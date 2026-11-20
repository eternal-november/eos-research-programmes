module
public import ContextualComposition.RepresentableKleisliGeneric
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePurePreframe
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliGeneric RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option linter.unusedSimpArgs false
section Generic
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {X Y Z W V : C} (d : X ⟶ Y) (f : Y ⟶ F.obj Z) (g : Z ⟶ F.obj W) (h : W ⟶ F.obj V)
def push : cmp F μ (d ≫ f) g ≅ d ≫ cmp F μ f g :=
  whiskerRightIso (α_ d f (F.map g)) (μ W) ≪≫ (α_ d (f ≫ F.map g) (μ W))
theorem linear :
    bend F μ D a (d ≫ f) g h ≪≫ push F μ d f (cmp F μ g h) =
    whiskerRightIso (whiskerRightIso (push F μ d f g) (F.map h)) (μ V) ≪≫
      push F μ d (cmp F μ f g) h ≪≫ whiskerLeftIso d (bend F μ D a f g h) := by
  apply Iso.ext
  simp only [bend,push,moveTail,moveHead,Iso.trans_hom,Iso.trans_inv,Iso.symm_inv,Iso.symm_hom,whiskerLeftIso_hom,
    whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
theorem natural₁ {f' : Y ⟶ F.obj Z} (t : f ⟶ f') :
    (((d ◁ t) ▷ F.map g) ▷ μ W) ≫ (push F μ d f' g).hom =
    (push F μ d f g).hom ≫ d ◁ ((t ▷ F.map g) ▷ μ W) := by
  simp only [push,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  bicategory
theorem natural₂ {g' : Z ⟶ F.obj W} (t : g ⟶ g') :
    ((d ≫ f) ◁ F.map₂ t) ▷ μ W ≫ (push F μ d f g').hom =
    (push F μ d f g).hom ≫ d ◁ ((f ◁ F.map₂ t) ▷ μ W) := by
  simp only [push,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  bicategory
variable {W₀ : C} (e : W₀ ⟶ X) (b : Y ⟶ X)
theorem twicePrefix :
    push F μ (e ≫ d) f g ≪≫ (α_ e d (cmp F μ f g)) =
    whiskerRightIso (whiskerRightIso (α_ e d f) (F.map g)) (μ W) ≪≫
      push F μ e (d ≫ f) g ≪≫ whiskerLeftIso e (push F μ d f g) := by
  apply Iso.ext
  simp only [push,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
end Generic
end ContextualComposition.GrothendieckStep.RepresentablePurePreframe
