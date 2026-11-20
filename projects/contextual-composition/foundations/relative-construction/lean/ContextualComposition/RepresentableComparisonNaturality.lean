module
public import ContextualComposition.RepresentableComparisonTransport
public import ContextualComposition.RepresentableUnitComparisonLaw
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonNaturality
open CategoryTheory CategoryTheory.Bicategory
open RepresentableComparisonTransport
open RepresentableKleisli (horizontal horizontal_id horizontal_comp)
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] {H : B → B → Type z} [∀ x y, Category.{q} (H x y)]
variable (D : Data H)
attribute [local simp] Functor.map_comp Category.assoc Iso.inv_hom_id_assoc Iso.hom_inv_id_assoc
theorem left {x y : B} {f g : H x y} (t : f ⟶ g) :
    W D (𝟙 (D.unit x)) t ≫ ((ops D).left g).hom = ((ops D).left f).hom ≫ t := by
  apply (D.fullfaithful x y).map_injective
  simp only [Functor.map_comp,leftCell,leftPort,leftImage,Iso.trans_hom,whiskerRightIso_hom,Category.assoc,
    Iso.inv_hom_id_assoc,whisker_exchange_assoc,leftUnitor_naturality]
theorem right {x y : B} {f g : H x y} (t : f ⟶ g) :
    W D t (𝟙 (D.unit y)) ≫ ((ops D).right g).hom = ((ops D).right f).hom ≫ t := by
  apply (D.fullfaithful x y).map_injective
  simp only [Functor.map_comp,rightCell,rightPort,rightImage,Iso.trans_hom,whiskerLeftIso_hom,Category.assoc,Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc,rightUnitor_naturality]
section
variable {x y z r : B} {f f' : H x y} {g g' : H y z} {h h' : H z r}
variable (s : f ⟶ f') (t : g ⟶ g') (u : h ⟶ h')
theorem leftThree : Y D (W D (W D s t) u) ≫ (head D f' g' h').hom =
    (head D f g h).hom ≫ horizontal (horizontal (Y D s) (Y D t)) (Y D u) := by
  simp only [head,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  rw [reassoc_of% (D.cmpNat (W D s t) u)]
  simp only [horizontal,Category.assoc]
  rw [whisker_exchange (D.cmpIso f' g').hom (Y D u)]
  have w := congrArg (fun j => j ▷ X D h) (D.cmpNat s t)
  simp only [comp_whiskerRight] at w
  rw [reassoc_of% w]
  rfl
theorem rightThree : Y D (W D s (W D t u)) ≫ (tail D f' g' h').hom =
    (tail D f g h).hom ≫ horizontal (Y D s) (horizontal (Y D t) (Y D u)) := by
  simp only [tail,Iso.trans_hom,whiskerLeftIso_hom,Category.assoc]
  rw [reassoc_of% (D.cmpNat s (W D t u))]
  simp only [horizontal,Category.assoc]
  rw [← Bicategory.whiskerLeft_comp,D.cmpNat t u,Bicategory.whiskerLeft_comp]
  rw [← whisker_exchange_assoc]
  rfl
theorem transportAssoc {J : Type*} [Category J]
    {p p' q q' x x' y y' : J}
    (A : p ≅ x) (A' : p' ≅ x') (B : q ≅ y) (B' : q' ≅ y')
    (a : x ≅ y) (a' : x' ≅ y') (tP : p ⟶ p') (tQ : q ⟶ q')
    (tX : x ⟶ x') (tY : y ⟶ y')
    (h : tP ≫ A'.hom = A.hom ≫ tX) (j : tQ ≫ B'.hom = B.hom ≫ tY)
    (k : tX ≫ a'.hom = a.hom ≫ tY) :
    tP ≫ (A' ≪≫ a' ≪≫ B'.symm).hom = (A ≪≫ a ≪≫ B.symm).hom ≫ tQ := by
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
  have w := RepresentableUnitComparisonLaw.reverseNat B B' tQ tY j
  rw [reassoc_of% h,reassoc_of% k,w]
theorem ambientNat : horizontal (horizontal (Y D s) (Y D t)) (Y D u) ≫
    (α_ (X D f') (X D g') (X D h')).hom =
    (α_ (X D f) (X D g) (X D h)).hom ≫ horizontal (Y D s) (horizontal (Y D t) (Y D u)) := by
  simp only [horizontal,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
theorem assoc {f f' : H x y} {g g' : H y z} {h h' : H z r} (p : f ⟶ f') (q : g ⟶ g') (v : h ⟶ h') :
    W D (W D p q) v ≫ ((ops D).assoc f' g' h').hom =
      ((ops D).assoc f g h).hom ≫ W D p (W D q v) := by
  apply (D.fullfaithful x r).map_injective
  simp only [Functor.map_comp,assocPort,assocImage]
  exact transportAssoc (head D f g h) (head D f' g' h') (tail D f g h) (tail D f' g' h')
    _ _ _ _ _ _ (leftThree D p q v) (rightThree D p q v) (ambientNat D p q v)
end
end ContextualComposition.GrothendieckStep.RepresentableComparisonNaturality
