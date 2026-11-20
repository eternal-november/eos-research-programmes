module
public import ContextualComposition.RepresentablePureAssociativity
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureAssocAnchor
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliGeneric RepresentablePureAssociativity
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : (X : C) → X ⟶ F.obj X)
variable (L : ∀ {X Y : C} (f : X ⟶ F.obj Y), cmp F μ (e X) f ≅ f)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {X Y Z W : C} (d : X ⟶ Y) (b : Y ⟶ Z) (k : Z ⟶ W)
local notation "X₀" => RepresentableKleisliGeneric.cmp F μ (J F e b) (J F e k)
local notation "Y₀" => J F e (b ≫ k)
theorem framed
    (j : X₀ ≅ Y₀)
    (u : RepresentableKleisliGeneric.cmp F μ (e Y) X₀ ⟶ RepresentableKleisliGeneric.cmp F μ (e Y) Y₀)
    (p : RepresentableKleisliGeneric.cmp F μ (e Y) X₀ ≅ X₀)
    (p' : RepresentableKleisliGeneric.cmp F μ (e Y) Y₀ ≅ Y₀)
    (rj : j = c F μ e L b k) (ru : u = cell F μ (𝟙 (e Y)) j.hom)
    (rp : p = L X₀) (rp' : p' = L Y₀)
    (n : u ≫ p'.hom = p.hom ≫ j.hom)
    (l : bend F μ D a (e Y) (J F e b) (J F e k) ≪≫ L X₀ = wr F μ (L (J F e b)) (J F e k)) :
    bend F μ D a (J F e d) (J F e b) (J F e k) ≪≫
      ws F μ (J F e d) (c F μ e L b k) ≪≫ c F μ e L d (b ≫ k) =
    wr F μ (c F μ e L d b) (J F e k) ≪≫ c F μ e L (d ≫ b) k ≪≫ whiskerRightIso (α_ d b k) (e W) := by
  subst j; subst u; subst p; subst p'
  exact assoc F μ e L D a d b k n l
end
end ContextualComposition.GrothendieckStep.RepresentablePureAssocAnchor
