module
public import ContextualComposition.RepresentablePentagonWord
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePentagonWordPasting
open CategoryTheory CategoryTheory.Bicategory
open RepresentablePentagonWord AmbientHorizontalNaturality
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local infixl:81 " ▹ " => whiskerRightIso
section
variable {C : Type*} [Bicategory C]
theorem swap {x y a b w : C} {p p' : x ⟶ y} {f : y ⟶ a} {g : a ⟶ w} {F : y ⟶ b} {G : b ⟶ w}
    (U : p ≅ p') (V : f ≫ g ≅ F ≫ G) :
    L p V ≪≫ U ▹ F ▹ G = U ▹ f ▹ g ≪≫ L p' V := by
  apply Iso.ext
  simp only [L,Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Category.assoc]
  rw [← associator_inv_naturality_left,whisker_exchange_assoc,associator_naturality_left_assoc]
def frame {x b c d w : C} (p : x ⟶ b) (a : b ⟶ c) (b₁ : c ⟶ d) (c₁ : d ⟶ w) :
    (((p ≫ a) ≫ b₁) ≫ c₁) ≅ p ≫ ((a ≫ b₁) ≫ c₁) :=
  (α_ p a b₁) ▹ c₁ ≪≫ (α_ p (a ≫ b₁) c₁)
theorem leftDistr {x y z : C} (p : x ⟶ y) {a b c : y ⟶ z} (u : a ≅ b) (v : b ≅ c) :
    whiskerLeftIso p (u ≪≫ v) = whiskerLeftIso p u ≪≫ whiskerLeftIso p v := by
  apply Iso.ext; simp only [Iso.trans_hom,whiskerLeftIso_hom,Bicategory.whiskerLeft_comp]
theorem rightDistr {x y z : C} {a b c : x ⟶ y} (u : a ≅ b) (v : b ≅ c) (p : y ⟶ z) :
    (u ≪≫ v) ▹ p = u ▹ p ≪≫ v ▹ p := by
  apply Iso.ext; simp only [Iso.trans_hom,whiskerRightIso_hom,comp_whiskerRight]
theorem carry {x y z w : C} (p : x ⟶ y) {r r' r'' : y ⟶ z} (q : z ⟶ w)
    (v : r ≅ r') (v' : r' ≅ r'') :
    (α_ p r q) ≪≫ whiskerLeftIso p ((v ≪≫ v') ▹ q) ≪≫ (α_ p r'' q).symm =
    (α_ p r q) ≪≫ whiskerLeftIso p (v ▹ q) ≪≫ (α_ p r' q).symm ≪≫
      (α_ p r' q) ≪≫ whiskerLeftIso p (v' ▹ q) ≪≫ (α_ p r'' q).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Category.assoc,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Iso.inv_hom_id_assoc]
end
end ContextualComposition.GrothendieckStep.RepresentablePentagonWordPasting
