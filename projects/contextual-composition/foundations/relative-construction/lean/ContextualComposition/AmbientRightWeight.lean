module
public import ContextualComposition.AmbientUnitWeight
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientRightWeight
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight AmbientWeightLetters
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (d : ContextadUnit.Data P)
set_option linter.defProp false in
def original :=
  let e := congrArg (· ≫ E S Y d) (InducedBicategory.hom_ext (AmbientBlockIteration.blockZero (S := S) f.hom)).symm
  framedInv (action S 1) e (comparison S (insert S d) (unitCart d) f)
theorem read : AmbientBoundaryReduction.RRead (i := 1) (j := 2) S f (kEta S d f) (rightUnit d) :=
  wrap (i := 1) (j := 2) f (rightUnit d) (kEta S d f).inv (cell S 1 (comparison S (insert S d) (unitCart d) f).inv)
    _ _ (original f d) (unitQ f (insert S d) (unitCart d))
end ContextualComposition.GrothendieckStep.AmbientRightWeight
