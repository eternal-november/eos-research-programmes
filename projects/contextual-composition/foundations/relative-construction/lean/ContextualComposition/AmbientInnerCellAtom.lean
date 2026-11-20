module
public import ContextualComposition.AmbientCellUnpack
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInnerCellAtom
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory TelescopeSquares
open NativeBlocks ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality AmbientFoldReading AmbientFlatWeight
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
open AmbientWeightLetters AmbientModificationAction
open AmbientWeightPicture AmbientHorizontalRead ContextadInsideCells AmbientFlatInside
open AmbientCellPictures
open AmbientCellUnpack
variable {a b : obj S 3 X ⟶ obj S 1 X} (t : a ⟶ b) {r s : Map S 3 1} (c : Cell r s)
variable (h : Reads (S := S) (X := X) (j := 3) (k := 1) t c)
variable (e : tot a = global (S := S) (i := 3) (j := 1) X r) (w : tot b = global (S := S) (i := 3) (j := 1) X s)
include h e w in
theorem packed : Diagram (X := X) (cell S 1 t) (insideCell 1 c) :=
  AmbientCellPictures.collect (S := S) (X := X) c t (v3 X) (v1 X) h e w
set_option linter.defProp false in
def core := extract (S := S) (X := X) (cell S 1 t) (insideCell 1 c) (packed t c h e w)
end ContextualComposition.GrothendieckStep.AmbientInnerCellAtom
