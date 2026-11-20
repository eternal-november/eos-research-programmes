module
public import ContextualComposition.AmbientActualIsoEdges
public import ContextualComposition.AmbientCanonViaLinks
public import ContextualComposition.AmbientScheduleEdges
public import ContextualComposition.AmbientFoldedAssocRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientPentagon
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
open AmbientActualIsoEdges AmbientIsoWords
noncomputable def long := (PA X d m C) ≪≫ (PB X d m C) ≪≫ (PC X d m C)
noncomputable def short := (PD X d m C) ≪≫ (PJ X m) ≪≫ (PE X d m C)
theorem leftFrame : long X d m C = AmbientHorizontalDiagrams.pentLong S d m C X := rfl
theorem rightFrame : short X d m C = AmbientHorizontalDiagrams.pentShort S d m C X := rfl
variable (h : PentagonLaw d m C)
set_option linter.defProp false in
def row := AmbientIsoFragments.pentagon (n := 4) X (pent1 d m C) (pent2 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (oneTwo d m C) (twoThree d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C)
  (PA X d m C) (PB X d m C) (PC X d m C) (PD X d m C) (PJ X m) (PE X d m C) 
  (rPA X d m C) (rPB X d m C) (rPC X d m C) (rPD X d m C) (rPJ X m) (rPE X d m C) (fromPentagon d m C h)
set_option linter.defProp false in
def fitted := faces (long X d m C) (short X d m C) (AmbientHorizontalDiagrams.pentLong S d m C X) (AmbientHorizontalDiagrams.pentShort S d m C X)
  (leftFrame X d m C) (rightFrame X d m C) (row X d m C h)
set_option linter.defProp false in
def unpack := sameHom (AmbientHorizontalDiagrams.pentLong S d m C X) (AmbientHorizontalDiagrams.pentShort S d m C X) (fitted X d m C h)
include h in
theorem original : Pentagon S d m C X := unpack X d m C h
end ContextualComposition.GrothendieckStep.AmbientPentagon
