module
public import ContextualComposition.AmbientNativeLetterFrame
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientConstraintRows
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientLetterRead
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
open AmbientNativeLetterFrame
variable (X : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def left := trace (i := 1) (j := 1) X C.left (presIso C.left.grade (fun _ h => h)) (fun _ h => h)
  (route S X (leftUnit d) (tensor m) _ m.cart (E S (obj S 1 X) d) (outerE S X d)) (idRoute S X 1).symm
  (AmbientHorizontalFrames.left S X d m C) rfl
set_option linter.defProp false in
def right := trace (i := 1) (j := 1) X C.right (presIso C.right.grade (fun _ h => h)) (fun _ h => h)
  (route S X (rightUnit d) (tensor m) _ m.cart (K S (E S X d)) (innerE S X d)) (idRoute S X 1).symm
  (AmbientHorizontalFrames.right S X d m C) rfl
set_option linter.defProp false in
def assoc := trace (i := 3) (j := 1) X C.assoc (assocCart m) (presIso C.assoc.grade.symm (assocCart m))
  (route S X (firstTwo m) (tensor m) _ m.cart (M S (obj S 1 X) m) (outerM S X m))
  (route S X (lastTwo m) (tensor m) _ m.cart (K S (M S X m)) (innerM S X m))
  (AmbientHorizontalFrames.assoc S X d m C) rfl
end ContextualComposition.GrothendieckStep.AmbientConstraintRows
