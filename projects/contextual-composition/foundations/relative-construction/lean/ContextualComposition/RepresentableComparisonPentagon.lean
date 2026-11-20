module
public import ContextualComposition.RepresentableComparisonNaturality
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableComparisonPentagon
open CategoryTheory CategoryTheory.Bicategory
open RepresentableComparisonTransport
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1150000
set_option linter.unusedSimpArgs false
universe u v w z q
variable {B : Type u} [Bicategory.{w,v} B] {H : B → B → Type z} [∀ x y, Category.{q} (H x y)]
variable (D : Data H)
local infixl:71 " ⋆ " => cmp D
variable {x y z r k : B} (f : H x y) (g : H y z) (h : H z r) (i : H r k)
def p0 := D.cmpIso ((f ⋆ g) ⋆ h) i ≪≫ whiskerRightIso (head D f g h) (X D i)
def p1 := D.cmpIso (f ⋆ (g ⋆ h)) i ≪≫ whiskerRightIso (tail D f g h) (X D i)
def p2 := D.cmpIso f ((g ⋆ h) ⋆ i) ≪≫ whiskerLeftIso (X D f) (head D g h i)
def p3 := D.cmpIso f (g ⋆ (h ⋆ i)) ≪≫ whiskerLeftIso (X D f) (tail D g h i)
def p4 := D.cmpIso (f ⋆ g) (h ⋆ i) ≪≫ whiskerRightIso (D.cmpIso f g) (X D (h ⋆ i)) ≪≫
  whiskerLeftIso (X D f ≫ X D g) (D.cmpIso h i)
theorem first :
    Y D (W D ((ops D).assoc f g h).hom (𝟙 i)) ≫ (p1 D f g h i).hom =
      (p0 D f g h i).hom ≫ (α_ (X D f) (X D g) (X D h)).hom ▷ X D i := by
  simp only [rightCell,assocPort,p1,p0,assocImage,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,
    comp_whiskerRight,Category.assoc,Iso.inv_hom_id_assoc,inv_hom_whiskerRight_assoc,Category.comp_id]
  simp only [ops,RepresentableComparisonTransport.cmp,Iso.inv_hom_id_assoc,inv_hom_whiskerRight,Category.comp_id]
theorem second :
    Y D ((ops D).assoc f (g ⋆ h) i).hom ≫ (p2 D f g h i).hom =
      (p1 D f g h i).hom ≫ (α_ (X D f) (X D g ≫ X D h) (X D i)).hom := by
  simp only [assocPort,p2,p1,assocImage,head,tail,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,whiskerRightIso_hom,
    whiskerLeftIso_hom,whiskerLeftIso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc,
    Iso.inv_hom_id_assoc,whiskerLeft_inv_hom_assoc]
  rw [associator_naturality_middle]
theorem third :
    Y D (W D (𝟙 f) ((ops D).assoc g h i).hom) ≫ (p3 D f g h i).hom =
      (p2 D f g h i).hom ≫ X D f ◁ (α_ (X D g) (X D h) (X D i)).hom := by
  simp only [leftCell,assocPort,p2,p3,assocImage,Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,
    Bicategory.whiskerLeft_comp,Category.assoc,Iso.inv_hom_id_assoc,whiskerLeft_inv_hom]
  simp only [ops,RepresentableComparisonTransport.cmp,Iso.inv_hom_id_assoc,whiskerLeft_inv_hom,Category.comp_id]
theorem fourth :
    Y D ((ops D).assoc (f ⋆ g) h i).hom ≫ (p4 D f g h i).hom =
      (p0 D f g h i).hom ≫ (α_ (X D f ≫ X D g) (X D h) (X D i)).hom := by
  simp only [assocPort,p4,p0,assocImage,head,tail,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,whiskerRightIso_hom,
    whiskerLeftIso_hom,whiskerLeftIso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc,Iso.inv_hom_id_assoc]
  rw [← whisker_exchange,whiskerLeft_inv_hom_assoc,← associator_naturality_left]
theorem fifth :
    Y D ((ops D).assoc f g (h ⋆ i)).hom ≫ (p3 D f g h i).hom =
      (p4 D f g h i).hom ≫ (α_ (X D f) (X D g) (X D h ≫ X D i)).hom := by
  simp only [assocPort,p3,p4,assocImage,head,tail,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,whiskerRightIso_hom,
    whiskerLeftIso_hom,whiskerLeftIso_inv,Bicategory.whiskerLeft_comp,Category.assoc,
    Iso.inv_hom_id_assoc,whiskerLeft_inv_hom_assoc]
  rw [associator_naturality_right]
theorem pentagon :
    W D ((ops D).assoc f g h).hom (𝟙 i) ≫ ((ops D).assoc f (g ⋆ h) i).hom ≫
        W D (𝟙 f) ((ops D).assoc g h i).hom =
      ((ops D).assoc (f ⋆ g) h i).hom ≫ ((ops D).assoc f g (h ⋆ i)).hom := by
  apply (D.fullfaithful x k).map_injective
  apply (cancel_mono (p3 D f g h i).hom).mp
  simp only [Functor.map_comp,Category.assoc]
  rw [third D f g h i,reassoc_of% (second D f g h i),reassoc_of% (first D f g h i)]
  rw [fifth D f g h i,reassoc_of% (fourth D f g h i),Bicategory.pentagon]
end ContextualComposition.GrothendieckStep.RepresentableComparisonPentagon
