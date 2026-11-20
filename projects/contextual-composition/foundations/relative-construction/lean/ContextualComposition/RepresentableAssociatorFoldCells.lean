module
public import ContextualComposition.RepresentableAssociatorPrefix
public import ContextualComposition.RepresentableUnitComparisonLaw
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableAssociatorFoldCells
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
section Generic
variable {C : Type*} [Bicategory C] (F : StrictPseudofunctor C C)
variable {a b c d : C} {x y : a ⟶ b} {p q : b ⟶ c} (m : c ⟶ d)
def split (x : a ⟶ b) (p : b ⟶ c) :=
  RepresentableStrictFold.unfoldThree F x p m
theorem first (t : x ⟶ y) :
    F.map₂ ((t ▷ p) ▷ m) ≫ (split F m y p).hom =
      (split F m x p).hom ≫ (F.map₂ t ▷ F.map p) ▷ F.map m := by
  simp only [split,RepresentableStrictFold.unfoldThree,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  have inner : F.map₂ (t ▷ p) ≫ (F.mapComp y p).hom =
      (F.mapComp x p).hom ≫ F.map₂ t ▷ F.map p := F.toPseudofunctor.toOplax.mapComp_naturality_left t p
  have outer : F.map₂ ((t ▷ p) ▷ m) ≫ (F.mapComp (y ≫ p) m).hom =
      (F.mapComp (x ≫ p) m).hom ≫ F.map₂ (t ▷ p) ▷ F.map m :=
    F.toPseudofunctor.toOplax.mapComp_naturality_left (t ▷ p) m
  rw [← Category.assoc (F.map₂ ((t ▷ p) ▷ m)),outer,Category.assoc,← comp_whiskerRight, inner,comp_whiskerRight]
theorem second (t : p ⟶ q) :
    F.map₂ ((x ◁ t) ▷ m) ≫ (split F m x q).hom =
      (split F m x p).hom ≫ (F.map x ◁ F.map₂ t) ▷ F.map m := by
  simp only [split,RepresentableStrictFold.unfoldThree,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  have inner : F.map₂ (x ◁ t) ≫ (F.mapComp x q).hom =
      (F.mapComp x p).hom ≫ F.map x ◁ F.map₂ t := F.toPseudofunctor.toOplax.mapComp_naturality_right x t
  have outer : F.map₂ ((x ◁ t) ▷ m) ≫ (F.mapComp (x ≫ q) m).hom =
      (F.mapComp (x ≫ p) m).hom ≫ F.map₂ (x ◁ t) ▷ F.map m :=
    F.toPseudofunctor.toOplax.mapComp_naturality_left (x ◁ t) m
  rw [← Category.assoc (F.map₂ ((x ◁ t) ▷ m)),outer,Category.assoc,← comp_whiskerRight, inner,comp_whiskerRight]
end Generic
end ContextualComposition.GrothendieckStep.RepresentableAssociatorFoldCells
