module
public import ContextualComposition.RepresentableTriangleNormalized
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableTriangleInterchange
open CategoryTheory CategoryTheory.Bicategory
open AmbientHorizontalNaturality AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientBicategory AmbientHorizontalFrames RepresentableKleisli RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
section General
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] {x y z w j : C}
variable {g : x ⟶ y} {p : x ⟶ z} {q : y ⟶ w} {G : z ⟶ w}
variable {m : z ⟶ x} {n N : w ⟶ y} {v : y ⟶ j}
variable (k : g ≫ q ≅ p ≫ G) (s : G ≫ n ≅ m ≫ g) (a : n ≫ v ≅ N ≫ v) (l : q ≫ N ≅ 𝟙 y)
def atom (v : y ⟶ j) (s : G ≫ n ≅ m ≫ g) (p : x ⟶ z) : ((p ≫ m) ≫ g) ≫ v ≅ (p ≫ G) ≫ (n ≫ v) :=
  moveTail p v s.symm
def finish (q : y ⟶ w) (N : w ⟶ y) (v : y ⟶ j) (l : q ≫ N ≅ 𝟙 y) :=
  (α_ q N v).symm ≪≫ whiskerRightIso l v ≪≫ (λ_ v)
def crossed : ((p ≫ m) ≫ g) ≫ v ≅ g ≫ v :=
  atom v s p ≪≫ whiskerLeftIso (p ≫ G) a ≪≫ whiskerRightIso k.symm (N ≫ v) ≪≫
  (α_ g q (N ≫ v)) ≪≫ whiskerLeftIso g (finish q N v l)
def swapped : ((p ≫ m) ≫ g) ≫ v ≅ g ≫ v :=
  atom v s p ≪≫ whiskerRightIso k.symm (n ≫ v) ≪≫ whiskerLeftIso (g ≫ q) a ≪≫
  (α_ g q (N ≫ v)) ≪≫ whiskerLeftIso g (finish q N v l)
theorem exchange : crossed k s a l = swapped k s a l := by
  apply Iso.ext
  simp only [crossed,swapped,Iso.trans_hom,whiskerLeftIso_hom,whiskerRightIso_hom,Iso.symm_hom]
  rw [whisker_exchange_assoc]
theorem frame :
    swapped k s a l = RepresentableTriangleNormalized.more (serial k s) v
      (middle q n v a ≪≫ whiskerRightIso l v ≪≫ (λ_ v)) := by
  apply Iso.ext
  simp only [swapped,atom,moveTail,RepresentableTriangleNormalized.more,finish,serial,middle,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerLeftIso_hom,whiskerRightIso_hom,whiskerLeftIso_inv,whiskerRightIso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
end General
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {D E : B} (g : KH S D E)
set_option linter.defProp false in
def original :=
  (exchange (kEta S T.unit g) (squareM S T.mult g) (assocIso T (yObj E)) (foldUnit (action S 1) (leftIso T (yObj E)))).trans
  ((frame (kEta S T.unit g) (squareM S T.mult g) (assocIso T (yObj E)) (foldUnit (action S 1) (leftIso T (yObj E)))).trans
    (RepresentableTriangleNormalized.original T g))
end ContextualComposition.GrothendieckStep.RepresentableTriangleInterchange
