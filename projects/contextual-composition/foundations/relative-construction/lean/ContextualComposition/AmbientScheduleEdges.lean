module
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientScheduleEdges
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
open AmbientNativeLetterFrame ContextadAppendCells
open AmbientScheduleFragment AmbientDeepIndices AmbientDisjointFrames
variable (X : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
set_option linter.defProp false in
def triSwitch := AmbientScheduleFragment.pre (n := 2) X C.assoc (assoc S X d m C) (K S (E S (obj S 1 X) d))
  (inside 1 (leftUnit d)) (AmbientConstraintRows.assoc X d m C) (frontEta S X d)
set_option linter.defProp false in
def triShort := AmbientScheduleFragment.post (n := 2) X (suffixCell C.right) (right S (obj S 1 X) d m C).hom m (AmbientOutsideLetters.right X d m C)
set_option linter.defProp false in
def pentOne := AmbientScheduleFragment.post (n := 4) X (suffixCell C.assoc) (assoc S (obj S 1 X) d m C).hom m (AmbientOutsideLetters.assoc X d m C)
set_option linter.defProp false in
def pentTwo := AmbientScheduleFragment.pre (n := 4) X C.assoc (assoc S X d m C) (K S (M S (obj S 1 X) m))
  (inside 1 (firstTwo m)) (AmbientConstraintRows.assoc X d m C) (frontMu S X m)
set_option linter.defProp false in
def pentFour := AmbientScheduleFragment.pre (n := 4) X C.assoc (assoc S X d m C) (M S (obj S 2 X) m)
  (suffix (firstTwo m)) (AmbientConstraintRows.assoc X d m C) (wideRead S X m)
set_option linter.defProp false in
def pentFive := AmbientScheduleFragment.pre (n := 4) X C.assoc (assoc S X d m C) (K S (K S (M S X m)))
  (inside 2 (tensor m)) (AmbientConstraintRows.assoc X d m C) (deepMu S X m)
end ContextualComposition.GrothendieckStep.AmbientScheduleEdges
