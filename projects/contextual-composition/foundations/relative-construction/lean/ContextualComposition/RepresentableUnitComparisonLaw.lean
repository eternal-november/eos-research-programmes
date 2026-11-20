module
public import ContextualComposition.RepresentableKleisliConstraints
public import ContextualComposition.AmbientLiteralMonadMaps
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableUnitComparisonLaw
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientMonadMaps
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
section General
variable {C D : Type*} [Bicategory C] [Bicategory D] {F G : Pseudofunctor C D} (τ : StrongTrans F G)
variable (a : ∀ X : C, F.obj X ⟶ G.obj X)
variable (b : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ a Y ≅ a X ≫ G.map f)
theorem natural (e : ∀ X, τ.app X = a X) (s : ∀ {X Y} (f : X ⟶ Y), HEq (τ.naturality f) (b f))
    {X Y : C} {f g : X ⟶ Y} (k : f ⟶ g) : F.map₂ k ▷ a Y ≫ (b g).hom = (b f).hom ≫ a X ◁ G.map₂ k := by
  cases (funext e).symm
  exact (congrArg ((F.map₂ k ▷ τ.app Y) ≫ ·) (congrArg Iso.hom (eq_of_heq (s g))).symm).trans
    ((τ.naturality_naturality k).trans (congrArg (· ≫ τ.app X ◁ G.map₂ k) (congrArg Iso.hom (eq_of_heq (s f)))))
theorem reverseNat {D : Type*} [Category D] {a b c d : D} (s : a ≅ b) (t : c ≅ d) (p : a ⟶ c) (q : b ⟶ d)
    (h : p ≫ t.hom = s.hom ≫ q) : s.inv ≫ p = q ≫ t.inv := by
  apply (cancel_mono t.hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,h,Iso.inv_hom_id_assoc]
end General
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {X Y : Obj.{u,u} B} {f g : X ⟶ Y} (k : f ⟶ g)
theorem etaPin (Z : Obj.{u,u} B) : (unitMap T).app Z = E S Z T.unit := AmbientMonadMapRead.etaApp S T.unit Z
set_option linter.defProp false in
def etaNatural := natural (F := II (B := B)) (G := AmbientMonadMaps.K S) (unitMap T) (fun Z => E S Z T.unit)
    (fun f => squareE S T.unit f) (etaPin T) (fun f => AmbientLiteralMonadMaps.eta T f) k
end ContextualComposition.GrothendieckStep.RepresentableUnitComparisonLaw
