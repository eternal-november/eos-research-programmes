module
public import ContextualComposition.AmbientFlatInside
public import ContextualComposition.AmbientFoldFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLiftedLetters
open CategoryTheory CategoryTheory.Functor Opposite CategoryTheory.Bicategory
open ContextadRoutes ContextadLawTransport ContextadModification ContextadNativeLaws ContextadOuterCharts
open AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientBicategory AmbientHorizontalRead AmbientLetterRead
open AmbientChartSplice AmbientFlatInside
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell ContextadLawTransport.rawCell ContextadInsideCells.insideCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def idTotal (n : Nat) := (congrArg tot (idRoute S X n).symm).trans (totalOper S X (identity n) (fun _ h => h))
set_option linter.defProp false in
def firstTotal := totalRoute X (i := 1) (j := 2) (k := 1) (E S (obj S 1 X) d) (leftUnit d) (tensor m) m.cart (outerE S X d)
set_option linter.defProp false in
def outerTotal := totalRoute X (i := 3) (j := 2) (k := 1) (M S (obj S 1 X) m) (firstTwo m) (tensor m) m.cart (outerM S X m)
set_option linter.defProp false in
def innerTotal := totalRoute X (i := 3) (j := 2) (k := 1) (K S (M S X m)) (lastTwo m) (tensor m) m.cart (innerM S X m)
end ContextualComposition.GrothendieckStep.AmbientLiftedLetters
