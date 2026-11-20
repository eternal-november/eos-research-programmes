module
public import ContextualComposition.RepresentableAssociatorLast
public import ContextualComposition.RepresentableMultiplicationFrame
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableLastAnchor
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliGeneric
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {V W X Y : C}
theorem withFrames (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h')
    (u : F.map h ⟶ F.map h') (v : F.map (F.map h) ⟶ F.map (F.map h'))
    (pl : F.obj (F.obj X) ⟶ F.obj X) (pr : F.obj (F.obj (F.obj Y)) ⟶ F.obj (F.obj Y))
    (s : F.map (F.map h) ≫ pr ≅ pl ≫ F.map h) (s' : F.map (F.map h') ≫ pr ≅ pl ≫ F.map h')
    (e : u = F.map₂ t) (m : v = F.map₂ (F.map₂ t))
    (el : pl = μ X) (er : pr = μ (F.obj Y))
    (es : HEq s (D h)) (es' : HEq s' (D h'))
    (n : s.inv ≫ v ▷ pr = pl ◁ u ≫ s'.inv) :
    cell F μ (𝟙 (cmp F μ f g)) t ≫ (bend F μ D a f g h').hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ (𝟙 g) t) := by
  subst pl; subst pr
  exact RepresentableAssociatorLast.exactLastBy F μ D a f g t u v e m (by
    rw [← eq_of_heq es,← eq_of_heq es']
    exact n)
theorem withNative (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h')
    (u : F.map h ⟶ F.map h') (v : F.map (F.map h) ⟶ F.map (F.map h'))
    (pl : F.obj (F.obj X) ⟶ F.obj X) (pr : F.obj (F.obj (F.obj Y)) ⟶ F.obj (F.obj Y))
    {j j' : F.obj (F.obj X) ⟶ F.obj (F.obj (F.obj Y))}
    (v' : j ⟶ j') (e₀ : F.map (F.map h) = j) (e₁ : F.map (F.map h') = j')
    (s : j ≫ pr ≅ pl ≫ F.map h) (s' : j' ≫ pr ≅ pl ≫ F.map h')
    (e : u = F.map₂ t) (m : v = F.map₂ (F.map₂ t))
    (el : pl = μ X) (er : pr = μ (F.obj Y))
    (es : HEq (RepresentableMultiplicationFrame.shift pr e₀ s) (D h))
    (es' : HEq (RepresentableMultiplicationFrame.shift pr e₁ s') (D h'))
    (n : v ≫ eqToHom e₁ = eqToHom e₀ ≫ v')
    (x : s.inv ≫ v' ▷ pr = pl ◁ u ≫ s'.inv) :
    cell F μ (𝟙 (cmp F μ f g)) t ≫ (bend F μ D a f g h').hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ (𝟙 g) t) :=
  withFrames F μ D a f g t u v pl pr (RepresentableMultiplicationFrame.shift pr e₀ s)
    (RepresentableMultiplicationFrame.shift pr e₁ s') e m el er es es'
    (RepresentableMultiplicationFrame.shiftedNat pr pl e₀ e₁ v v' u s s' n x)
end
end ContextualComposition.GrothendieckStep.RepresentableLastAnchor
