module
public import ContextualComposition.RepresentablePentagonCore
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonPaths
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliGeneric RepresentablePentagonWord
open AmbientHorizontalDiagrams
open scoped CategoryTheory.Bicategory
local infixl:81 " ▹ " => whiskerRightIso
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {U V X Y Z : C}
variable (f : U ⟶ F.obj V) (g : V ⟶ F.obj X) (h : X ⟶ F.obj Y) (i : Y ⟶ F.obj Z)
def originalLong :=
  (bend F μ D a f g h ▹ F.map i ▹ μ Z) ≪≫
  bend F μ D a f (cmp F μ g h) i ≪≫
  (whiskerLeftIso f (F.map₂Iso (bend F μ D a g h i)) ▹ μ Z)
def originalShort :=
  bend F μ D a (cmp F μ f g) h i ≪≫ bend F μ D a f g (cmp F μ h i)
theorem front :
    cmp F μ (cmp F μ (cmp F μ f g) h) i =
      (f ≫ F.map g) ≫ (((((μ X ≫ F.map h) ≫ μ Y) ≫ F.map i) ≫ μ Z)) := by
  simp only [RepresentableKleisliGeneric.cmp,Category.assoc]
theorem back :
    (f ≫ F.map g) ≫ ((((F.map (F.map h) ≫ F.map (F.map (F.map i))) ≫ F.map (F.map (μ Z))) ≫ F.map (μ Z)) ≫ μ Z) =
      cmp F μ f (cmp F μ g (cmp F μ h i)) := by
  simp only [RepresentableKleisliGeneric.cmp,F.map_comp,Category.assoc]
def bridge {x y : F.obj (F.obj X) ⟶ F.obj Z}
    (u : x ≅ y)
    (s : cmp F μ (cmp F μ (cmp F μ f g) h) i = (f ≫ F.map g) ≫ x)
    (t : (f ≫ F.map g) ≫ y = cmp F μ f (cmp F μ g (cmp F μ h i))) :=
  eqToIso s ≪≫ whiskerLeftIso (f ≫ F.map g) u ≪≫ eqToIso t
def wordLong :=
  bridge F μ f g h i (long (D h).symm (D i).symm (foldMap F (D i)).symm (a Y) (a Z) (foldMap F (a Z)))
    (front F μ f g h i) (back F μ f g h i)
def wordShort :=
  bridge F μ f g h i (short (D h).symm (D i).symm (D (F.map i)).symm (D (μ Z)).symm (a Z))
    (front F μ f g h i) (back F μ f g h i)
end ContextualComposition.GrothendieckStep.RepresentableKleisliPentagonPaths
