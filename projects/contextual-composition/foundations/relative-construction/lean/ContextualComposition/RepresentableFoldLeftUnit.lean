module
public import ContextualComposition.RepresentableKleisliConstraints
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableFoldLeftUnit
open CategoryTheory CategoryTheory.Bicategory
open ContextualComposition.GrothendieckStep.AmbientHorizontalDiagrams
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
section General
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable {a b c d : C} {f : a ⟶ b} {p : b ⟶ c} {q : c ⟶ b} {e : a ⟶ d} {u : d ⟶ c}
variable (s : f ≫ p ≅ e ≫ u) (r : p ≫ q ≅ 𝟙 b)
def bare := whiskerRightIso s.symm q ≪≫ (α_ f p q) ≪≫ whiskerLeftIso f r ≪≫ (ρ_ f)
def foldBare :=
    F.mapComp (e ≫ u) q ≪≫ whiskerRightIso (F.mapComp e u) (F.map q) ≪≫
    whiskerRightIso (foldMap F s).symm (F.map q) ≪≫ (α_ (F.map f) (F.map p) (F.map q)) ≪≫
    whiskerLeftIso (F.map f) (foldUnit F r) ≪≫ (ρ_ (F.map f))
theorem folded : F.map₂Iso (bare s r) = foldBare F s r := by
  apply Iso.ext
  simp only [bare,foldBare,foldMap,foldUnit,Iso.trans_hom,Iso.symm_hom,Iso.trans_inv,Iso.symm_inv,
    whiskerRightIso_hom,whiskerLeftIso_hom,PrelaxFunctor.map₂Iso_hom,PrelaxFunctor.map₂Iso_inv,PrelaxFunctor.map₂_comp,
    Pseudofunctor.map₂_whisker_left,Pseudofunctor.map₂_whisker_right,Pseudofunctor.map₂_associator,Pseudofunctor.map₂_right_unitor,
    comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc,
    hom_inv_whiskerRight_assoc,Iso.inv_hom_id_assoc]
end General
end ContextualComposition.GrothendieckStep.RepresentableFoldLeftUnit
