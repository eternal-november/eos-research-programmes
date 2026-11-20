module
public import ContextualComposition.RepresentableUnitComparisonLaw
public import ContextualComposition.RepresentableRightUnitor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableLeftUnitor
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad AmbientHorizontalDiagrams AmbientMonadMaps
open RepresentableKleisli RepresentableKleisliConstraints RepresentableUnitComparisonLaw
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section Generic
variable {C : Type*} [Bicategory C] {a b c d : C} {f g : a ⟶ b} {p : b ⟶ c} {q : c ⟶ b}
variable {x y : a ⟶ c} (s : f ≫ p ≅ x) (t : g ≫ p ≅ y)
variable (j : x ⟶ y) (k : f ⟶ g) (r : p ≫ q ≅ 𝟙 b)
def auxiliary (v : x ⟶ y) :=
    (v ▷ q) ≫ (whiskerRightIso t.symm q ≪≫ (α_ g p q) ≪≫ whiskerLeftIso g r ≪≫ (ρ_ g)).hom
theorem pasting (h : j ≫ t.inv = s.inv ≫ k ▷ p) :
    auxiliary t r j = (whiskerRightIso s.symm q ≪≫ (α_ f p q) ≪≫ whiskerLeftIso f r ≪≫ (ρ_ f)).hom ≫ k := by
  simp only [auxiliary,Iso.trans_hom,whiskerRightIso_hom,Iso.symm_hom,Category.assoc]
  rw [← Category.assoc (j ▷ q), ← comp_whiskerRight, h, comp_whiskerRight, Category.assoc]
  simpa only [Iso.trans_hom,whiskerLeftIso_hom,Category.assoc] using congrArg ((s.inv ▷ q) ≫ ·) (RepresentableRightUnitor.natural k r)
end Generic
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable (T : Data S) {A D : B} {f g : KH S A D} (k : f ⟶ g)
theorem inverseUnit :
    E S (yObj A) T.unit ◁ AmbientBicategory.cell S 1 k ≫ (squareE S T.unit g).inv =
      (squareE S T.unit f).inv ≫ k ▷ E S (KObj S D) T.unit := by
  symm
  apply reverseNat
  exact etaNatural T k
theorem original :
    composeCell T (𝟙 (unit T A)) k ≫ (leftUnit T g).hom = (leftUnit T f).hom ≫ k := by
  have h : composeCell T (𝟙 (unit T A)) k = (unit T A ◁ AmbientBicategory.cell S 1 k) ▷ M S (yObj D) T.mult := by
    unfold composeCell
    rw [id_whiskerRight,Category.id_comp]
  rw [h]
  exact pasting (squareE S T.unit f) (squareE S T.unit g) (unit T A ◁ AmbientBicategory.cell S 1 k) k
    (leftIso T (yObj D)) (inverseUnit T k)
end ContextualComposition.GrothendieckStep.RepresentableLeftUnitor
