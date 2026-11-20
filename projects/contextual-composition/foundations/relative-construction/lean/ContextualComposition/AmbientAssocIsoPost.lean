module
public import ContextualComposition.AmbientPostIso
public import ContextualComposition.AmbientFoldedAssocCell
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFramedCells
public import ContextualComposition.AmbientInnerCellAtom
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientAssocIsoPost
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
open AmbientFramedCells
variable {U V : Obj.{u,v} B} {a : obj S 3 X ⟶ U} {b : U ⟶ obj S 1 X} {a' : obj S 3 X ⟶ V} {b' : V ⟶ obj S 1 X}
variable (t : a ≫ b ≅ a' ≫ b') {r s : Map S 3 1} (c : Cell r s)
variable (m : ContextadTotal.Native S)
set_option linter.defProp false in
def step (h : AmbientFoldedAssocCell.Fold X t c) :=
  AmbientPostIso.read (n := 4) (r := inside 1 r) (s := inside 1 s) X (insideCell 1 c) (foldMap (action S 1) t) m h
end ContextualComposition.GrothendieckStep.AmbientAssocIsoPost
