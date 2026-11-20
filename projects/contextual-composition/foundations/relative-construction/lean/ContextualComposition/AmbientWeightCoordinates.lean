module
public import ContextualComposition.AmbientFlatWeight
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientWeightLetters
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
section General
variable {i j : Nat} {a b c d : obj S i X ⟶ obj S j Y} (r : Map S i j)
def QRead (t : a ⟶ b) : Prop := ∀ x, Aligned (atRaw (X := X) (Y := Y) (i := i) (j := j) S t x) ((AmbientComparisonRead.q S r f).app x)
theorem wrap (t : a ⟶ d) (n : b ⟶ c) (e : a = b) (h : c = d) (eq : t = eqToHom e ≫ n ≫ eqToHom h)
    (p : QRead f r n) : QRead f r t := by
  subst t; exact fun x => (stays (z := n) (S := S) (X := X) (Y := Y) (i := i) (j := j) e h x).trans (p x)
end General
end ContextualComposition.GrothendieckStep.AmbientWeightLetters
