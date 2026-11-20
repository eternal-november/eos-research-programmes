module
public import ContextualComposition.AmbientSquareGuard
public import ContextualComposition.AmbientInsideMulWeight
public import ContextualComposition.AmbientInnerWeightAtom
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideGuard
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight AmbientWeightLetters
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
variable {i j : Nat} {a b : obj S i X ⟶ obj S j Y} (r : Map S i j)
theorem pin (t : a ≅ b) (h : QRead (i := i) (j := j) f r t.inv) : AmbientSquareGuard.Guard (i := i) (j := j) f r t := h
variable {u v : obj S i X ⟶ obj S j Y}
theorem wrapped (t : a ≅ b) (n : u ⟶ v) (e : b = u) (k : v = a) (eq : t.inv = eqToHom e ≫ n ≫ eqToHom k)
    (h : QRead (i := i) (j := j) f r n) : AmbientSquareGuard.Guard (i := i) (j := j) f r t :=
  pin f r t (wrap (i := i) (j := j) f r t.inv n e k eq h)
set_option linter.defProp false in
def actual := wrapped (i := 3) (j := 2) f (lastTwo m) (kMu S m f) (cell S 1 (comparison S (tensor m) m.cart f).inv) _ _ (AmbientInsideMulWeight.original f m) (AmbientInnerWeightAtom.core f (tensor m) m.cart)
end ContextualComposition.GrothendieckStep.AmbientInsideGuard
