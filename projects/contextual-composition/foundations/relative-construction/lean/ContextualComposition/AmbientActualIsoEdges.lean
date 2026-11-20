module
public import ContextualComposition.AmbientUnitIsoPost
public import ContextualComposition.AmbientAssocIsoPost
public import ContextualComposition.AmbientIsoFragments
public import ContextualComposition.AmbientLeftFoldedRead
public import ContextualComposition.AmbientCanonViaLinks
public import ContextualComposition.AmbientScheduleEdges
public import ContextualComposition.AmbientFoldedAssocRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientActualIsoEdges
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
open ContextadSchedule AmbientCanonViaLinks ContextadDisjointCut
open AmbientIsoFragments
set_option linter.defProp false in
def cross := AmbientScheduleFragment.post (n := 4) X (disjoint (tensor m) (tensor m) m.cart) (AmbientExchangeDemand.interchange X m).hom m (AmbientFourToTwo.exchange X m)
noncomputable def TA := middle (K S (E S (obj S 1 X) d)) _ _ (assoc S X d m C)
set_option linter.defProp false in
def rTA := AmbientIsoFragments.hom (n := 2) X (triSwitch d m C) (middle (K S (E S (obj S 1 X) d)) _ _ (assoc S X d m C)) (AmbientScheduleEdges.triSwitch X d m C)
noncomputable def TL := whiskerRightIso (foldUnit (action S 1) (left S X d m C)) (M S X m)
set_option linter.defProp false in
def rTL := AmbientUnitIsoPost.step X (left S X d m C) C.left m (AmbientLeftFoldedRead.cell X d m C)
noncomputable def TR := whiskerRightIso (right S (obj S 1 X) d m C) (M S X m)
set_option linter.defProp false in
def rTR := AmbientIsoFragments.whisk (n := 2) X (triRight d m C) (right S (obj S 1 X) d m C) (M S X m) (AmbientScheduleEdges.triShort X d m C)
noncomputable def PA := whiskerRightIso (assoc S (obj S 1 X) d m C) (M S X m)
set_option linter.defProp false in
def rPA := AmbientIsoFragments.whisk (n := 4) X (pent1 d m C) (assoc S (obj S 1 X) d m C) (M S X m) (AmbientScheduleEdges.pentOne X d m C)
noncomputable def PB := middle (K S (M S (obj S 1 X) m)) _ _ (assoc S X d m C)
set_option linter.defProp false in
def rPB := AmbientIsoFragments.hom (n := 4) X (pent2 d m C) (middle (K S (M S (obj S 1 X) m)) _ _ (assoc S X d m C)) (AmbientScheduleEdges.pentTwo X d m C)
noncomputable def PC := whiskerRightIso (foldMap (action S 1) (assoc S X d m C)) (M S X m)
set_option linter.defProp false in
def rPC := AmbientAssocIsoPost.step X (assoc S X d m C) C.assoc m (AmbientFoldedAssocRead.cell X d m C)
noncomputable def PD := middle (M S (obj S 2 X) m) _ _ (assoc S X d m C)
set_option linter.defProp false in
def rPD := AmbientIsoFragments.hom (n := 4) X (pent4 d m C) (middle (M S (obj S 2 X) m) _ _ (assoc S X d m C)) (AmbientScheduleEdges.pentFour X d m C)
noncomputable def PJ := whiskerRightIso (AmbientExchangeDemand.interchange X m) (M S X m)
set_option linter.defProp false in
def rPJ := AmbientIsoFragments.whisk (n := 4) X (exchangeEdge m) (AmbientExchangeDemand.interchange X m) (M S X m) (cross X m)
noncomputable def PE := middle (K S (K S (M S X m))) _ _ (assoc S X d m C)
set_option linter.defProp false in
def rPE := AmbientIsoFragments.hom (n := 4) X (pent5 d m C) (middle (K S (K S (M S X m))) _ _ (assoc S X d m C)) (AmbientScheduleEdges.pentFive X d m C)
end ContextualComposition.GrothendieckStep.AmbientActualIsoEdges
