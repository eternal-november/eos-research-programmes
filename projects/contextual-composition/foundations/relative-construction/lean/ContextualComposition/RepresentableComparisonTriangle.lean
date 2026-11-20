module
public import ContextualComposition.RepresentableComparisonPentagon
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonTriangle
open CategoryTheory CategoryTheory.Bicategory
open RepresentableComparisonTransport RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] {H : B → B → Type z} [∀ x y, Category.{q} (H x y)]
variable (D : Data H)
variable {x y z : B} (f : H x y) (g : H y z)
def pre :=
  head D f (D.unit y) g ≪≫ whiskerRightIso (whiskerLeftIso (X D f) (D.unitIso y)) (X D g)
def post :=
  tail D f (D.unit y) g ≪≫ whiskerLeftIso (X D f) (whiskerRightIso (D.unitIso y) (X D g))
theorem pivot :
    Y D ((ops D).assoc f (D.unit y) g).hom ≫ (post D f g).hom =
      (pre D f g).hom ≫ (α_ (X D f) (𝟙 y) (X D g)).hom := by
  simp only [assocPort,assocImage,pre,post,Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,
    Category.assoc,Iso.inv_hom_id_assoc,associator_naturality_middle]
theorem upper :
    Y D (W D (𝟙 f) ((ops D).left g).hom) ≫ (D.cmpIso f g).hom =
      (post D f g).hom ≫ X D f ◁ (λ_ (X D g)).hom := by
  simp only [leftCell,leftPort,leftImage,tail,post,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,
    Category.assoc,Iso.inv_hom_id,Bicategory.whiskerLeft_comp,Category.comp_id]
  rfl
theorem lower :
    Y D (W D ((ops D).right f).hom (𝟙 g)) ≫ (D.cmpIso f g).hom =
      (pre D f g).hom ≫ (ρ_ (X D f)).hom ▷ X D g := by
  simp only [rightCell,rightPort,rightImage,head,pre,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,
    Category.assoc,Iso.inv_hom_id,comp_whiskerRight,Category.comp_id]
  rfl
theorem triangle :
    ((ops D).assoc f (D.unit y) g).hom ≫ W D (𝟙 f) ((ops D).left g).hom =
      W D ((ops D).right f).hom (𝟙 g) := by
  apply (D.fullfaithful x z).map_injective
  apply (cancel_mono (D.cmpIso f g).hom).mp
  simp only [Functor.map_comp,Category.assoc]
  rw [upper D f g,lower D f g,reassoc_of% (pivot D f g),Bicategory.triangle]
theorem W_id {x y z : B} (f : H x y) (g : H y z) : W D (𝟙 f) (𝟙 g) = 𝟙 (RepresentableComparisonTransport.cmp D f g) :=
  D.mult.map_id (f,g)
theorem laws : Laws (ops D) := by
  constructor
  · intro a b i j t; exact RepresentableComparisonNaturality.left D t
  · intro a b i j t; exact RepresentableComparisonNaturality.right D t
  · intro a b c d i j t k l
    simpa only [W_id,ops,RepresentableComparisonTransport.cmp,RepresentableBicategoryAssembly.cmp,
      RepresentableBicategoryAssembly.lW,RepresentableBicategoryAssembly.rW,RepresentableBicategoryAssembly.compCell] using RepresentableComparisonNaturality.assoc D t (𝟙 k) (𝟙 l)
  · intro a b c d i j k t l
    exact RepresentableComparisonNaturality.assoc D (𝟙 i) t (𝟙 l)
  · intro a b c d i j k l t
    simpa only [W_id,ops,RepresentableComparisonTransport.cmp,RepresentableBicategoryAssembly.cmp,
      RepresentableBicategoryAssembly.lW,RepresentableBicategoryAssembly.rW,RepresentableBicategoryAssembly.compCell] using RepresentableComparisonNaturality.assoc D (𝟙 i) (𝟙 j) t
  · intro a b c p q; exact triangle D p q
  · intro a b c d e p q r s; exact RepresentableComparisonPentagon.pentagon D p q r s
@[instance_reducible]
def build : Bicategory B := RepresentableBicategoryAssembly.build (ops D) (laws D)
end ContextualComposition.GrothendieckStep.RepresentableComparisonTriangle
