module
public import ContextualComposition.AmbientInnerWeightAtom
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideMulWeight
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
set_option linter.defProp false in
def original :=
  let e := congrArg (· ≫ M S Y m) (twice S f)
  framedInv (action S 1) e (comparison S (tensor m) m.cart f)
theorem read : AmbientBoundaryReduction.RRead (i := 3) (j := 2) S f (kMu S m f) (lastTwo m) :=
  wrap (i := 3) (j := 2) f (lastTwo m) (kMu S m f).inv (cell S 1 (comparison S (tensor m) m.cart f).inv)
    _ _ (original f m) (AmbientInnerWeightAtom.core f (tensor m) m.cart)
end ContextualComposition.GrothendieckStep.AmbientInsideMulWeight
