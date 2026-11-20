module
public import ContextualComposition.RepresentableUnitComparisonLaw
public import ContextualComposition.AmbientOperationLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableMultiplicationFrame
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open AmbientCoordinates ContextadRoutes ContextadNativeLaws ContextadOuterCharts
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
section Generic
variable {C D : Type*} [Bicategory C] [Bicategory D] {a b : C} {f g : a ⟶ b}
theorem cellHEq {F G : StrictPseudofunctor C D} (E : F = G) (x : f ⟶ g) : HEq (F.map₂ x) (G.map₂ x) := by cases E; rfl
theorem pathNat {D : Type*} [Category D] {a b a' b' : D} (e : a = a') (v : b = b')
    (t : a ⟶ b) (w : a' ⟶ b') (h : HEq t w) : t ≫ eqToHom v = eqToHom e ≫ w := by
  subst a'; subst b'; rw [eq_of_heq h]; simp
variable {a b c x : D} {r r' r₂ r₂' : a ⟶ b} {s s' : x ⟶ c} (m : b ⟶ c) (l : a ⟶ x)
variable (e : r = r₂) (v : r' = r₂') (t : r ⟶ r') (w : r₂ ⟶ r₂') (z : s ⟶ s')
variable (p : r₂ ≫ m ≅ l ≫ s) (q : r₂' ≫ m ≅ l ≫ s')
def shift {x y z : D} {f g : x ⟶ y} {h : x ⟶ z} (u : y ⟶ z) (e : f = g) (p : g ≫ u ≅ h) : f ≫ u ≅ h :=
  eqToIso (congrArg (· ≫ u) e) ≪≫ p
theorem shiftedNat (h : t ≫ eqToHom v = eqToHom e ≫ w)
    (j : p.inv ≫ w ▷ m = l ◁ z ≫ q.inv) :
    (shift m e p).inv ≫ t ▷ m = l ◁ z ≫ (shift m v q).inv := by
  have aux : eqToHom e.symm ≫ t = w ≫ eqToHom v.symm :=
    RepresentableUnitComparisonLaw.reverseNat (eqToIso e) (eqToIso v) t w h
  have aux' := congrArg (· ▷ m) aux
  simp only [comp_whiskerRight,eqToHom_whiskerRight] at aux'
  simp only [shift,Iso.trans_inv,eqToIso.inv,Category.assoc]
  rw [aux',← Category.assoc p.inv,j,Category.assoc]
end Generic
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {X Y : Obj.{u,u} B} {f g : X ⟶ Y} (k : f ⟶ g)
set_option linter.defProp false in
def originalCell := cellHEq (AmbientIteratedFunctor.succ S 1) k
theorem iterateCell :
    AmbientBicategory.cell S 1 (AmbientBicategory.cell S 1 k) ≫ eqToHom (twice S g) =
       eqToHom (twice S f) ≫ AmbientBicategory.cell S 2 k :=
  pathNat (twice S f) (twice S g) _ _ (originalCell k)
set_option linter.defProp false in
def rawNatural :=
  shiftedNat (a := obj S 2 X) (b := obj S 2 Y) (x := obj S 1 X) (c := obj S 1 Y)
    (M S Y T.mult) (M S X T.mult) (twice S f) (twice S g)
    (AmbientBicategory.cell S 1 (AmbientBicategory.cell S 1 k)) (AmbientBicategory.cell S 2 k) (AmbientBicategory.cell S 1 k)
    (comparison S (tensor T.mult) T.mult.cart f) (comparison S (tensor T.mult) T.mult.cart g)
    (iterateCell k) (AmbientOperationLaws.modification S (tensor T.mult) T.mult.cart k)
theorem squareShift {Z W : Obj.{u,u} B} (f : Z ⟶ W) :
    squareM S T.mult f = shift (M S W T.mult) (twice S f) (comparison S (tensor T.mult) T.mult.cart f) := rfl
end ContextualComposition.GrothendieckStep.RepresentableMultiplicationFrame
