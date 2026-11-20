module
public import ContextualComposition.AmbientFunctorCorner
public import ContextualComposition.AmbientFramedCells
public import ContextualComposition.AmbientInnerCellAtom
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFoldedAssocCell
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
variable (h : Native (i := 3) (j := 1) (u := a ≫ b) (v := a' ≫ b') X c t)
variable (e : AmbientFunctorCorner.Corner (i := 3) (j := 1) X r (a ≫ b))
variable (w : AmbientFunctorCorner.Corner (i := 3) (j := 1) X s (a' ≫ b'))
set_option linter.defProp false in
def central := AmbientInnerCellAtom.core (S := S) (X := X) t.hom c h e w
def Fold : Prop := Trace (i := 4) (j := 2) (r := inside 1 r) (s := inside 1 s) X (insideCell 1 c) (foldMap (action S 1) t).hom
include h e w in
theorem trace : Fold X t c := AmbientFramedCells.close (i := 4) (j := 2) X (insideCell 1 c) (foldMap (action S 1) t).hom
  (cell S 1 t.hom) _ _ (AmbientFoldFrames.mapHom (action S 1) t) (central X t c h e w)
end ContextualComposition.GrothendieckStep.AmbientFoldedAssocCell
