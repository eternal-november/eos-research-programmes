module
public import ContextualComposition.RepresentableTriangleCorner
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableTriangleNormalized
open CategoryTheory CategoryTheory.Bicategory
open AmbientHorizontalNaturality AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientBicategory AmbientHorizontalFrames RepresentableKleisli RepresentableTriangleCorner
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u
section General
variable {C : Type*} [Bicategory C] {x y z : C} {g : x ⟶ y} {p : x ⟶ x} {q : y ⟶ y}
variable (s : g ≫ q ≅ p ≫ g) (l : p ≅ 𝟙 x) (r : q ≅ 𝟙 y) (m : y ⟶ z)
def more (w : q ≫ m ≅ m) : (p ≫ g) ≫ m ≅ g ≫ m :=
  whiskerRightIso s.symm m ≪≫ (α_ g q m) ≪≫ whiskerLeftIso g w
theorem reconcile (w : q ≫ m ≅ m) (e : w.hom = (whiskerRightIso r m ≪≫ (λ_ m)).hom)
    (h : Square s (AmbientHorizontalNaturality.identity g) l r) :
    more s m w = whiskerRightIso (direct (g := g) l) m := by
  have e' : w = whiskerRightIso r m ≪≫ (λ_ m) := Iso.ext e
  subst w
  rw [← collapse s l r h]
  apply Iso.ext
  simp only [more,through,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,whiskerLeftIso_hom,Bicategory.whiskerLeft_comp,comp_whiskerRight,Category.assoc]
  bicategory
end General
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {D E : B} (g : KH S D E)
set_option linter.defProp false in
def original :=
  reconcile (serial (kEta S T.unit g) (squareM S T.mult g))
    (rightIso T (yObj D)) (rightIso T (KObj S E)) (M S (yObj E) T.mult)
    (triLong S T.unit T.mult T.constraints (yObj E))
    (T.laws.triangle (yObj E)) (T.laws.right_natural g)
end ContextualComposition.GrothendieckStep.RepresentableTriangleNormalized
