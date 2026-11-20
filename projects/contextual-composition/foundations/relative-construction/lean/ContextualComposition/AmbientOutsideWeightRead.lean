module
public import ContextualComposition.AmbientSuffixWeights
public import ContextualComposition.AmbientOrdinaryUnitRead
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientOutsideWeightRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S)
set_option linter.defProp false in
def unit := AmbientSuffixWeights.two f (squareE S d (K S f)) (insert S d) (AmbientOrdinaryUnitRead.unit (K S f) d)
set_option linter.defProp false in
def mul := AmbientSuffixWeights.three f (squareM S m (K S f)) (tensor m) (AmbientBoundaryReduction.muRead S (K S f) m)
end ContextualComposition.GrothendieckStep.AmbientOutsideWeightRead
