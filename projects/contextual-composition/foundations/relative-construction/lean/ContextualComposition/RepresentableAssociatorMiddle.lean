module
public import ContextualComposition.RepresentableAssociatorTailFirst
public import ContextualComposition.RepresentableKleisliGeneric
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableAssociatorMiddle
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliConstraints RepresentableAssociatorPrefix
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
section Generic
variable {C : Type*} [Bicategory C] {a b c d j w : C}
variable (f : a ⟶ b) (m : c ⟶ d) (k : d ⟶ j) (n : j ⟶ w)
variable {p p' : b ⟶ c} {l l' : b ⟶ j} (t : p ⟶ p') (u : l ⟶ l')
theorem frameNat :
    ((((f ◁ t) ▷ m) ▷ k) ▷ n) ≫ (frameIn f p' m k n).hom =
    (frameIn f p m k n).hom ≫ f ◁ (((t ▷ m) ▷ k) ▷ n) := by
  have w1 := congrArg (fun v => (v ▷ k) ▷ n) (associator_naturality_middle f t m)
  have w2 := congrArg (fun v => v ▷ n) (associator_naturality_middle f (t ▷ m) k)
  simp only [comp_whiskerRight] at w1 w2
  simp only [frameIn,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  rw [← Category.assoc ((((f ◁ t) ▷ m) ▷ k) ▷ n),w1,Category.assoc]
  rw [← Category.assoc (((f ◁ (t ▷ m)) ▷ k) ▷ n),w2,Category.assoc]
  rw [associator_naturality_middle]
variable (bdy : (((p ≫ m) ≫ k) ≫ n) ≅ l ≫ n) (bdy' : (((p' ≫ m) ≫ k) ≫ n) ≅ l' ≫ n)
theorem natural (eq : ((t ▷ m) ▷ k) ▷ n ≫ bdy'.hom = bdy.hom ≫ u ▷ n) :
    ((((f ◁ t) ▷ m) ▷ k) ▷ n) ≫ (factored p' m k n l' bdy' f).hom =
    (factored p m k n l bdy f).hom ≫ (f ◁ u) ▷ n := by
  simp only [factored,Iso.trans_hom,whiskerLeftIso_hom,Iso.symm_hom,Category.assoc]
  rw [← Category.assoc ((((f ◁ t) ▷ m) ▷ k) ▷ n),frameNat f m k n t,Category.assoc]
  rw [← Category.assoc (f ◁ (((t ▷ m) ▷ k) ▷ n)),← Bicategory.whiskerLeft_comp,eq,
    Bicategory.whiskerLeft_comp,Category.assoc,associator_inv_naturality_middle]
end Generic
open RepresentableKleisliGeneric
section Specialize
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {V W X Y : C}
theorem foldNaturality {g g' : W ⟶ F.obj X} (t : g ⟶ g') (h : X ⟶ F.obj Y) :
    ((F.map₂ t ▷ F.map (F.map h)) ▷ F.map (μ Y)) ≫ eqToHom (fold F μ g' h).symm =
      eqToHom (fold F μ g h).symm ≫ F.map₂ (cell F μ t (𝟙 h)) := by
  have ff := firstFold F μ t h
  rw [frame,frame] at ff
  exact (RepresentableUnitComparisonLaw.reverseNat _ _ _ _ ff).symm
def secondBody (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :=
  body (F.map g) (μ X) (F.map h) (μ Y) (F.map (F.map h)) (μ (F.obj Y)) (F.map (μ Y))
    (D h).symm (a Y) (F.map (cmp F μ g h)) (fold F μ g h).symm
theorem tailNatural {g g' : W ⟶ F.obj X} (t : g ⟶ g') (h : X ⟶ F.obj Y) :
    (((F.map₂ t ▷ μ X) ▷ F.map h) ▷ μ Y) ≫ (secondBody F μ D a g' h).hom =
      (secondBody F μ D a g h).hom ≫ F.map₂ (cell F μ t (𝟙 h)) ▷ μ Y :=
  RepresentableAssociatorTailFirst.bodyNat _ _ _ _ _ _ _ _ _ _ _ _ (foldNaturality F μ t h)
theorem frameBend (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) (h : X ⟶ F.obj Y) :
    bend F μ D a f g h = factored (F.map g) (μ X) (F.map h) (μ Y) (F.map (cmp F μ g h)) (secondBody F μ D a g h) f := by
  rw [shape]
  exact factor _ _ _ _ _ _ _ _ _ _ _ _
theorem exactMiddle (f : V ⟶ F.obj W) {g g' : W ⟶ F.obj X} (t : g ⟶ g') (h : X ⟶ F.obj Y) :
    cell F μ (cell F μ (𝟙 f) t) (𝟙 h) ≫ (bend F μ D a f g' h).hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ t (𝟙 h)) := by
  rw [RepresentableKleisliGeneric.first,second,second,frameBend,frameBend]
  exact natural f _ _ _ (F.map₂ t) _ _ _ (tailNatural F μ D a t h)
end Specialize
end ContextualComposition.GrothendieckStep.RepresentableAssociatorMiddle
