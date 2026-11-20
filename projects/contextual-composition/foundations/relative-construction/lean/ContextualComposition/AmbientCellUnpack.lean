module
public import ContextualComposition.AmbientCellPictures
public import ContextualComposition.AmbientFoldReading
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCellUnpack
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
variable {a b : obj S 4 X ⟶ obj S 2 X} (t : a ⟶ b) {r s : Map S 4 2} (c : Cell r s)
def Diagram : Prop :=
  let J := v1 (S := S) X
  letI := J.iso
  Picture (v3 (S := S) X).F J.F (totalCell t.hom.as) (rawCell (S := S) (i := 4) (j := 2) (r := r) (s := s) (underlying X) c).hom
theorem extract (h : Diagram (X := X) t c) : Reads (S := S) (X := X) (j := 4) (k := 2) t c := h
end ContextualComposition.GrothendieckStep.AmbientCellUnpack
