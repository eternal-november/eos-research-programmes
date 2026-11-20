module
public import ContextualComposition.AmbientFoldedUnit
public import ContextualComposition.AmbientInsideUnitCell
public import ContextualComposition.AmbientConstraintRows
public import ContextualComposition.AmbientFlatInside
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLeftFoldedCell
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
def Fold : Prop := Reads (S := S) (X := X) (j := 2) (k := 2) (r := inside 1 r) (s := inside 1 s) (foldUnit (action S 1) t).hom (insideCell 1 c)
theorem trace (h : Native (i := 1) (j := 1) X c t)
    (e : tot (a ≫ b) = global (S := S) (i := 1) (j := 1) X r) (w : tot (𝟙 (obj S 1 X)) = global (S := S) (i := 1) (j := 1) X s) :
    Fold X t c :=
  AmbientFoldedUnit.foldLeft X t (insideCell 1 c) (AmbientInsideUnitCell.unit X c t.hom h e w)
end ContextualComposition.GrothendieckStep.AmbientLeftFoldedCell
