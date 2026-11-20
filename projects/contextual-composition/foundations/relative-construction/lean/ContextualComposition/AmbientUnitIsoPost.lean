module
public import ContextualComposition.AmbientPostIso
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientLeftFoldedCell
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientUnitIsoPost
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open AmbientBicategory AmbientCoordinates AmbientHorizontalDiagrams AmbientFoldFrames AmbientHorizontalRead AmbientLetterRead
open ContextadRoutes ContextadLawTransport ContextadInsideCells NativeBlocks
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
open AmbientHorizontalFrames AmbientNativeLetterFrame
variable {U : Obj.{u,v} B} {a : obj S 1 X ⟶ U} {b : U ⟶ obj S 1 X} (t : a ≫ b ≅ 𝟙 _)
variable {r s : Map S 1 1} (c : Cell r s)
variable (m : ContextadTotal.Native S)
set_option linter.defProp false in
def step (h : AmbientLeftFoldedCell.Fold X t c) :=
  AmbientPostIso.read (n := 2) (r := inside 1 r) (s := inside 1 s) X (insideCell 1 c) (foldUnit (action S 1) t) m h
end ContextualComposition.GrothendieckStep.AmbientUnitIsoPost
