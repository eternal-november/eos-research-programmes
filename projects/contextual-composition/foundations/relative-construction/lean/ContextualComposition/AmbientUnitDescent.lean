module
public import ContextualComposition.AmbientUnitBends
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitSquare
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
variable {a : obj S 1 X ⟶ obj S 2 X} {b : obj S 1 Y ⟶ obj S 2 Y}
variable (r : Map S 1 2) (c : Cell (comp r (tensor m)) (ContextadRoutes.identity 1))
variable (e : global X r = tot a) (w : global Y r = tot b)
variable (s : K S f ≫ b ≅ a ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
noncomputable def constr (Z : Obj.{u,v} B) (u : obj S 1 Z ⟶ obj S 2 Z) (j : global Z r = tot u) :=
  reframe (installed m r c Z u j) (idRoute S Z 1).symm (AmbientNativeModification.cmp c (cart m r c) (fun _ h => h) Z)
def Result : Prop := Square (serial s (squareM S m f)) (AmbientHorizontalNaturality.identity (K S f))
  (constr m r c X a e) (constr m r c Y b w)
set_option linter.defProp false in
def carried := transport (a := K S f) (b := AmbientBicategory.map S 1 f) rfl
  (installed m r c X a e) (installed m r c Y b w) (idRoute S X 1).symm (idRoute S Y 1).symm
  _ _ _ _ (sourceSquare c (cart m r c) (fun _ h => h) f)
section Replace
variable {D : Type*} [Bicategory D] {i j k l : D} {v : i ⟶ k} {z : j ⟶ l} {p q : i ⟶ j} {p' q' : k ⟶ l}
variable {s t : v ≫ p' ≅ p ≫ z} {u w : v ≫ q' ≅ q ≫ z} {c : p ≅ q} {d : p' ≅ q'}
theorem replace (h : s = t) (k : u = w) (a : Square t w c d) : Square s u c d := by simpa only [h,k] using a
end Replace
end ContextualComposition.GrothendieckStep.AmbientUnitSquare
