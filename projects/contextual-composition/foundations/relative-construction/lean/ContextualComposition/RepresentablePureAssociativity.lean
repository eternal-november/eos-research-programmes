module
public import ContextualComposition.RepresentablePureBend
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureAssociativity
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliGeneric RepresentablePurePreframe RepresentablePureBend
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1350000
set_option linter.unusedSimpArgs false
local infixl:81 " ▹ " => whiskerRightIso
section
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : (X : C) → X ⟶ F.obj X)
variable (L : ∀ {X Y : C} (f : X ⟶ F.obj Y), RepresentableKleisliGeneric.cmp F μ (e X) f ≅ f)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {X Y Z W : C}
abbrev J {X Y : C} (d : X ⟶ Y) := d ≫ e Y
def c {X Y Z : C} (d : X ⟶ Y) (b : Y ⟶ Z) :
    RepresentableKleisliGeneric.cmp F μ (J F e d) (J F e b) ≅ J F e (d ≫ b) :=
  pre F μ e L d (J F e b) ≪≫ (α_ d b (e Z)).symm
def ws {X Y Z : C} (p : X ⟶ F.obj Y) {g h : Y ⟶ F.obj Z} (t : g ≅ h) :=
  whiskerLeftIso p (F.map₂Iso t) ▹ μ Z
def wr {X Y Z : C} {f f' : X ⟶ F.obj Y} (t : f ≅ f') (g : Y ⟶ F.obj Z) :=
  t ▹ F.map g ▹ μ Z
variable (d : X ⟶ Y) (b : Y ⟶ Z) (k : Z ⟶ W)
theorem moveNat
    (n : cell F μ (𝟙 (e Y)) (c F μ e L b k).hom ≫ (L (J F e (b ≫ k))).hom =
      (L (RepresentableKleisliGeneric.cmp F μ (J F e b) (J F e k))).hom ≫ (c F μ e L b k).hom) :
    ws F μ (J F e d) (c F μ e L b k) ≪≫ pre F μ e L d (J F e (b ≫ k)) =
      pre F μ e L d (RepresentableKleisliGeneric.cmp F μ (J F e b) (J F e k)) ≪≫ whiskerLeftIso d (c F μ e L b k) := by
  apply Iso.ext
  rw [Iso.trans_hom,Iso.trans_hom,whiskerLeftIso_hom]
  have j := natural F μ e L d (c F μ e L b k).hom n
  rw [RepresentableKleisliGeneric.second] at j
  exact j
theorem assoc
    (n : cell F μ (𝟙 (e Y)) (c F μ e L b k).hom ≫ (L (J F e (b ≫ k))).hom =
      (L (RepresentableKleisliGeneric.cmp F μ (J F e b) (J F e k))).hom ≫ (c F μ e L b k).hom)
    (l : bend F μ D a (e Y) (J F e b) (J F e k) ≪≫ L (RepresentableKleisliGeneric.cmp F μ (J F e b) (J F e k)) =
      wr F μ (L (J F e b)) (J F e k)) :
    bend F μ D a (J F e d) (J F e b) (J F e k) ≪≫
      ws F μ (J F e d) (c F μ e L b k) ≪≫ c F μ e L d (b ≫ k) =
    wr F μ (c F μ e L d b) (J F e k) ≪≫ c F μ e L (d ≫ b) k ≪≫ ((α_ d b k) ▹ e W) := by
  have aa := congrArg Iso.hom (moveNat F μ e L d b k n)
  have bb := congrArg Iso.hom (right F μ e L D a d (J F e b) (J F e k) l)
  have cc := congrArg Iso.hom (preCompose F μ e L d b (J F e k))
  apply Iso.ext
  simp only [c,wr,ws,J,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,whiskerLeftIso_hom,
    whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_inv,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc] at aa bb cc ⊢
  rw [reassoc_of% aa,reassoc_of% bb,← reassoc_of% cc]
  bicategory
end
end ContextualComposition.GrothendieckStep.RepresentablePureAssociativity
