module
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePentagonCorner
open CategoryTheory CategoryTheory.Bicategory
open AmbientHorizontalNaturality AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientBicategory AmbientHorizontalFrames RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u
section General
variable {D : Type*} [Category D] {x y z w : D}
variable (s : x ≅ y) (t : z ≅ w) (l : y ≅ w) (r : x ≅ z)
theorem turn (h : r.hom ≫ t.hom = s.hom ≫ l.hom) : l ≪≫ t.symm = s.symm ≪≫ r := by
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom]
  apply (cancel_mono t.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,h,Iso.inv_hom_id_assoc]
end General
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable (T : Data S) {X Y : Obj.{u,u} B} (f : X ⟶ Y)
set_option linter.defProp false in
def original :=
  turn (serial (muK S T.mult f) (squareM S T.mult f)) (serial (kMu S T.mult f) (squareM S T.mult f))
    (whiskerRightIso (assocIso T X) (K S f))
    (whiskerLeftIso (K S (K S (K S f))) (assocIso T Y))
    (T.laws.assoc_natural f)
end ContextualComposition.GrothendieckStep.RepresentablePentagonCorner
