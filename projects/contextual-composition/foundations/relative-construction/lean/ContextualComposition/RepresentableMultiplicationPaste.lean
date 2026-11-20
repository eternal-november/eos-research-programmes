module
public import ContextualComposition.RepresentableMultiplicationFrame
public import ContextualComposition.RepresentableKleisliGeneric
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableMultiplicationPaste
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientCoordinates ContextadRoutes ContextadNativeLaws ContextadOuterCharts
open RepresentableMultiplicationFrame
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
section Generic
variable {C : Type*} [Bicategory C] {a b c x y z : C}
variable {p p' : a ⟶ b} {q q' : b ⟶ c} {r r' : a ⟶ c}
variable {u : x ⟶ y} {v : y ⟶ z} {w : x ⟶ z}
variable {l : a ⟶ x} {m : b ⟶ y} {n : c ⟶ z}
def paste (e : r = p ≫ q) (j : u ≫ v = w) (α : p ≫ m ≅ l ≫ u) (β : q ≫ n ≅ m ≫ v) : r ≫ n ≅ l ≫ w :=
  eqToIso (congrArg (· ≫ n) e) ≪≫ (α_ p q n) ≪≫ whiskerLeftIso p β ≪≫
    (α_ p m v).symm ≪≫ whiskerRightIso α v ≪≫ (α_ l u v) ≪≫ eqToIso (congrArg (l ≫ ·) j)
theorem shiftPaste (A : p = p') (B : q = q') (W : r = r')
    (e : r = p ≫ q) (e' : r' = p' ≫ q') (j : u ≫ v = w)
    (s : p' ≫ m ≅ l ≫ u) (t : q' ≫ n ≅ m ≫ v) :
    shift n W (paste e' j s t) = paste e j (shift m A s) (shift n B t) := by
  subst p'; subst q'; subst r'
  simp only [shift, eqToIso_refl, Iso.refl_trans]
end Generic
section Preface
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F G : StrictPseudofunctor C C)
variable (m : ∀ X : C, F.obj X ⟶ G.obj X)
variable (D : ∀ {X Y : C} (x : X ⟶ Y), F.map x ≫ m Y ≅ m X ≫ G.map x)
variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
theorem pasteEq :
    AmbientPseudonaturality.pasted F G m D f g =
      paste (F.map_comp f g) (G.map_comp f g).symm (D f) (D g) := by
  apply Iso.ext
  simp only [AmbientPseudonaturality.pasted,paste,Iso.trans_hom,Iso.symm_hom,whiskerRightIso_hom,
    whiskerLeftIso_hom,Strict.associator_eqToIso,eqToIso.hom,eqToIso.inv,eqToHom_trans,eqToHom_trans_assoc]
end Preface
end ContextualComposition.GrothendieckStep.RepresentableMultiplicationPaste
