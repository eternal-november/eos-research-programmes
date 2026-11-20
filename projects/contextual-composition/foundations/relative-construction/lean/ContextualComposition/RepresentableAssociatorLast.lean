module
public import ContextualComposition.RepresentableAssociatorMiddle
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableAssociatorLast
open CategoryTheory CategoryTheory.Bicategory
open RepresentableAssociatorPrefix RepresentableKleisliGeneric RepresentableAssociatorTailFirst
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
section Generic
variable {C : Type*} [Bicategory C] {b c d e j w : C}
variable (p : b ⟶ c) (m : c ⟶ d) (n : j ⟶ w)
variable {k k' : d ⟶ j} {h h' : c ⟶ e} (q : e ⟶ j) (r : e ⟶ j)
variable (s : m ≫ k ≅ h ≫ q) (s' : m ≫ k' ≅ h' ≫ q) (a : q ≫ n ≅ r ≫ n)
variable (u : k ⟶ k') (v : h ⟶ h')
theorem atomNat (H : m ◁ u ≫ s'.hom = s.hom ≫ v ▷ q) :
    (m ◁ u) ▷ n ≫ (bodyAtom m k' n h' q r s' a).hom =
      (bodyAtom m k n h q r s a).hom ≫ (v ▷ r) ▷ n := by
  simp only [bodyAtom,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,Category.assoc]
  rw [← Category.assoc ((m ◁ u) ▷ n),← comp_whiskerRight,H,comp_whiskerRight,Category.assoc,
    associator_naturality_left_assoc,← Category.assoc (v ▷ (q ≫ n)),← whisker_exchange,Category.assoc,
    associator_inv_naturality_left]
theorem frameLast :
    ((p ≫ m) ◁ u) ▷ n ≫ (RepresentableAssociatorTailFirst.frame n p m k').hom =
    (RepresentableAssociatorTailFirst.frame n p m k).hom ≫ p ◁ ((m ◁ u) ▷ n) := by
  simp only [RepresentableAssociatorTailFirst.frame,Iso.trans_hom,whiskerRightIso_hom]
  bicategory
theorem frameMid :
    ((p ◁ v) ▷ r) ▷ n ≫ (RepresentableAssociatorTailFirst.frame n p h' r).hom =
    (RepresentableAssociatorTailFirst.frame n p h r).hom ≫ p ◁ ((v ▷ r) ▷ n) := by
  simp only [RepresentableAssociatorTailFirst.frame,Iso.trans_hom,whiskerRightIso_hom]
  bicategory
variable {l l' : b ⟶ j} (E : (p ≫ h) ≫ r = l) (E' : (p ≫ h') ≫ r = l') (t : l ⟶ l')
theorem tailNat (H : m ◁ u ≫ s'.hom = s.hom ≫ v ▷ q)
    (J : (p ◁ v) ▷ r ≫ eqToHom E' = eqToHom E ≫ t) :
    ((p ≫ m) ◁ u) ▷ n ≫ (body p m k' n h' q r s' a l' E').hom =
    (body p m k n h q r s a l E).hom ≫ t ▷ n := by
  rw [normalize,normalize]
  simp only [norm,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,eqToIso.hom,Category.assoc]
  rw [← Category.assoc (((p ≫ m) ◁ u) ▷ n),frameLast p m n u,Category.assoc]
  rw [← Category.assoc (p ◁ ((m ◁ u) ▷ n)),← Bicategory.whiskerLeft_comp,atomNat m n q r s s' a u v H,
    Bicategory.whiskerLeft_comp,Category.assoc]
  have W := RepresentableUnitComparisonLaw.reverseNat (RepresentableAssociatorTailFirst.frame n p h r) (RepresentableAssociatorTailFirst.frame n p h' r) (((p ◁ v) ▷ r) ▷ n)
    (p ◁ ((v ▷ r) ▷ n)) (frameMid p n r v)
  rw [← Category.assoc (p ◁ ((v ▷ r) ▷ n)),← W,Category.assoc,← comp_whiskerRight,J,comp_whiskerRight]
variable {o : C} (f : o ⟶ b)
theorem frameInLast :
    ((((f ≫ p) ≫ m) ◁ u) ▷ n) ≫ (frameIn f p m k' n).hom =
    (frameIn f p m k n).hom ≫ f ◁ (((p ≫ m) ◁ u) ▷ n) := by
  simp only [frameIn,Iso.trans_hom,whiskerRightIso_hom]
  bicategory
variable (bdy : (((p ≫ m) ≫ k) ≫ n) ≅ l ≫ n) (bdy' : (((p ≫ m) ≫ k') ≫ n) ≅ l' ≫ n)
theorem outerNat (H : ((p ≫ m) ◁ u) ▷ n ≫ bdy'.hom = bdy.hom ≫ t ▷ n) :
    ((((f ≫ p) ≫ m) ◁ u) ▷ n) ≫ (factored p m k' n l' bdy' f).hom =
    (factored p m k n l bdy f).hom ≫ (f ◁ t) ▷ n := by
  simp only [factored,Iso.trans_hom,whiskerLeftIso_hom,Iso.symm_hom,Category.assoc]
  rw [← Category.assoc ((((f ≫ p) ≫ m) ◁ u) ▷ n),frameInLast p m n u f,Category.assoc]
  rw [← Category.assoc (f ◁ (((p ≫ m) ◁ u) ▷ n)),← Bicategory.whiskerLeft_comp,H,
    Bicategory.whiskerLeft_comp,Category.assoc,associator_inv_naturality_middle]
end Generic
section Specialize
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (D : ∀ {X Y : C} (f : X ⟶ Y), F.map (F.map f) ≫ μ Y ≅ μ X ≫ F.map f)
variable (a : ∀ X, μ (F.obj X) ≫ μ X ≅ F.map (μ X) ≫ μ X)
variable {V W X Y : C}
variable (natD : ∀ {i j : C} {u v : i ⟶ j} (t : u ⟶ v),
    μ i ◁ F.map₂ t ≫ (D v).inv = (D u).inv ≫ F.map₂ (F.map₂ t) ▷ μ j)
theorem foldLast (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h') :
    (F.map g ◁ F.map₂ (F.map₂ t)) ▷ F.map (μ Y) ≫ eqToHom (fold F μ g h').symm =
      eqToHom (fold F μ g h).symm ≫ F.map₂ (cell F μ (𝟙 g) t) := by
  have ff := secondFold F μ g t
  rw [RepresentableKleisliGeneric.frame,RepresentableKleisliGeneric.frame] at ff
  exact (RepresentableUnitComparisonLaw.reverseNat _ _ _ _ ff).symm
theorem exactLastAt (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h')
    (n : μ X ◁ F.map₂ t ≫ (D h').inv = (D h).inv ≫ F.map₂ (F.map₂ t) ▷ μ (F.obj Y)) :
    cell F μ (𝟙 (cmp F μ f g)) t ≫ (bend F μ D a f g h').hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ (𝟙 g) t) := by
  rw [RepresentableKleisliGeneric.second,RepresentableKleisliGeneric.second,
    RepresentableAssociatorMiddle.frameBend,RepresentableAssociatorMiddle.frameBend]
  exact outerNat _ _ _ (F.map₂ t) _ f _ _
    (tailNat _ _ _ _ _ _ _ _ (F.map₂ t) (F.map₂ (F.map₂ t)) _ _ _ n (foldLast F μ g t))
theorem exactLastBy (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h')
    (u : F.map h ⟶ F.map h') (v : F.map (F.map h) ⟶ F.map (F.map h'))
    (e : u = F.map₂ t) (m : v = F.map₂ (F.map₂ t))
    (n : (D h).inv ≫ v ▷ μ (F.obj Y) = μ X ◁ u ≫ (D h').inv) :
    cell F μ (𝟙 (cmp F μ f g)) t ≫ (bend F μ D a f g h').hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ (𝟙 g) t) := by
  subst u; subst v
  exact exactLastAt F μ D a f g t n.symm
include natD in
theorem exactLast (f : V ⟶ F.obj W) (g : W ⟶ F.obj X) {h h' : X ⟶ F.obj Y} (t : h ⟶ h') :
    cell F μ (𝟙 (cmp F μ f g)) t ≫ (bend F μ D a f g h').hom =
    (bend F μ D a f g h).hom ≫ cell F μ (𝟙 f) (cell F μ (𝟙 g) t) :=
  exactLastAt F μ D a f g t (natD t)
end Specialize
end ContextualComposition.GrothendieckStep.RepresentableAssociatorLast
