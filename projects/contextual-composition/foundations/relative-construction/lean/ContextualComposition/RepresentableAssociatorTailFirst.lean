module
public import ContextualComposition.RepresentableAssociatorFoldCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableAssociatorTailFirst
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableKleisliConstraints RepresentableAssociatorPrefix
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
section Generic
variable {C : Type*} [Bicategory C] {b c d e j w : C}
variable (m : c ⟶ d) (k : d ⟶ j) (n : j ⟶ w)
variable (h : c ⟶ e) (q : e ⟶ j) (r : e ⟶ j) (s : m ≫ k ≅ h ≫ q) (t : q ≫ n ≅ r ≫ n)
variable {p : b ⟶ c} {l : b ⟶ j} (eq : (p ≫ h) ≫ r = l)
def bodyAtom : (m ≫ k) ≫ n ≅ (h ≫ r) ≫ n :=
  whiskerRightIso s n ≪≫ (α_ h q n) ≪≫ whiskerLeftIso h t ≪≫ (α_ h r n).symm
def frame (p : b ⟶ c) (m : c ⟶ d) (k : d ⟶ j) :=
  whiskerRightIso (α_ p m k) n ≪≫ (α_ p (m ≫ k) n)
def norm : (((p ≫ m) ≫ k) ≫ n) ≅ l ≫ n :=
  frame n p m k ≪≫ whiskerLeftIso p (bodyAtom m k n h q r s t) ≪≫ (frame n p h r).symm ≪≫
    whiskerRightIso (eqToIso eq) n
theorem normalize : body p m k n h q r s t l eq = norm m k n h q r s t eq := by
  apply Iso.ext
  simp only [body,norm,frame,bodyAtom,moveTail,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_hom]
  bicategory
variable {p' : b ⟶ c} (v : p ⟶ p')
theorem frameNat : ((v ▷ m) ▷ k) ▷ n ≫ (frame n p' m k).hom =
    (frame n p m k).hom ≫ v ▷ ((m ≫ k) ≫ n) := by
  have w := congrArg (fun t => t ▷ n) (associator_naturality_left v m k)
  simp only [comp_whiskerRight] at w
  simp only [frame,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  rw [← Category.assoc (((v ▷ m) ▷ k) ▷ n),w,Category.assoc,associator_naturality_left]
variable {l' : b ⟶ j} (eq' : (p' ≫ h) ≫ r = l') (u : l ⟶ l')
theorem bodyNat (hEq : (v ▷ h) ▷ r ≫ eqToHom eq' = eqToHom eq ≫ u) :
    ((v ▷ m) ▷ k) ▷ n ≫ (body p' m k n h q r s t l' eq').hom =
      (body p m k n h q r s t l eq).hom ≫ u ▷ n := by
  rw [normalize,normalize]
  simp only [norm,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,
    eqToIso.hom,Category.assoc]
  rw [← Category.assoc (((v ▷ m) ▷ k) ▷ n),frameNat m k n v,Category.assoc]
  rw [← Category.assoc (v ▷ ((m ≫ k) ≫ n)),← whisker_exchange,Category.assoc]
  have bb := RepresentableUnitComparisonLaw.reverseNat (frame n p h r) (frame n p' h r) (((v ▷ h) ▷ r) ▷ n)
    (v ▷ ((h ≫ r) ≫ n)) (frameNat h r n v)
  rw [← Category.assoc (v ▷ ((h ≫ r) ≫ n)),← bb,Category.assoc,← comp_whiskerRight,hEq,comp_whiskerRight]
end Generic
end ContextualComposition.GrothendieckStep.RepresentableAssociatorTailFirst
