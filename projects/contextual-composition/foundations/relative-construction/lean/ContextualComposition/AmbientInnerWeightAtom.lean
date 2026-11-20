module
public import ContextualComposition.AmbientWeightUnpack
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInnerWeightAtom
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
open AmbientWeightLetters AmbientModificationAction
open AmbientWeightPicture
open AmbientWeightUnpack
variable (r : Map S 2 1) (p : gradeCart r)
theorem packed : Diagram f (cell S 1 (comparison S r p f).inv) (inside 1 r) :=
  collect f r p (v2 X) (v1 Y)
set_option linter.defProp false in
def core := extract f (cell S 1 (comparison S r p f).inv) (inside 1 r) (packed f r p)
end ContextualComposition.GrothendieckStep.AmbientInnerWeightAtom
