module
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableTriangleCorner
open CategoryTheory CategoryTheory.Bicategory
open AmbientHorizontalNaturality AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientBicategory AmbientHorizontalFrames RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u
section General
variable {C : Type*} [Bicategory C] {x y z : C} {g : x ⟶ y} {p : x ⟶ x} {q : y ⟶ y}
variable (s : g ≫ q ≅ p ≫ g) (l : p ≅ 𝟙 x) (r : q ≅ 𝟙 y)
def through := s.symm ≪≫ whiskerLeftIso g r ≪≫ (ρ_ g)
def direct := whiskerRightIso l g ≪≫ (λ_ g)
theorem collapse (h : Square s (AmbientHorizontalNaturality.identity g) l r) :
    through s r = direct (g := g) l := by
  apply Iso.ext
  simp only [through,direct,Iso.trans_hom,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom]
  have h' := congrArg (fun k => s.inv ≫ k ≫ (λ_ g).hom) (show g ◁ r.hom ≫ (AmbientHorizontalNaturality.identity g).hom = s.hom ≫ l.hom ▷ g from h)
  simpa only [AmbientHorizontalNaturality.identity,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] using h'
end General
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {X Y : Obj.{u,u} B} (g : X ⟶ Y)
theorem originalCorner :
    through (serial (kEta S T.unit g) (squareM S T.mult g)) (rightIso T Y) =
    direct (g := K S g) (rightIso T X) :=
  collapse (serial (kEta S T.unit g) (squareM S T.mult g)) (rightIso T X) (rightIso T Y) (T.laws.right_natural g)
end ContextualComposition.GrothendieckStep.RepresentableTriangleCorner
