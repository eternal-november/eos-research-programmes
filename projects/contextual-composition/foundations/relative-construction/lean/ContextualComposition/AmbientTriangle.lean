module
public import ContextualComposition.AmbientActualIsoEdges
public import ContextualComposition.AmbientCanonViaLinks
public import ContextualComposition.AmbientScheduleEdges
public import ContextualComposition.AmbientLeftFoldedRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientTriangle
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
open ContextadSchedule AmbientCanonViaLinks
open AmbientActualIsoEdges AmbientIsoWords
noncomputable def long := (TA X d m C) ≪≫ (TL X d m C) ≪≫ (λ_ _)
noncomputable def short := (TR X d m C) ≪≫ (λ_ _)
theorem leftFrame : long X d m C = AmbientHorizontalDiagrams.triLong S d m C X := rfl
theorem rightFrame : short X d m C = AmbientHorizontalDiagrams.triShort S d m C X := rfl
variable (h : TriangleLaw d m C)
set_option linter.defProp false in
def row := AmbientIsoFragments.triangle (n := 2) X (triSwitch d m C) (triLeft d m C) (triRight d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C)
  (TA X d m C) (TL X d m C) (TR X d m C) (λ_ _)
  (rTA X d m C) (rTL X d m C) (rTR X d m C) (fromTriangle d m C h)
set_option linter.defProp false in
def fitted := faces (long X d m C) (short X d m C) (AmbientHorizontalDiagrams.triLong S d m C X) (AmbientHorizontalDiagrams.triShort S d m C X)
  (leftFrame X d m C) (rightFrame X d m C) (row X d m C h)
set_option linter.defProp false in
def unpack := sameHom (AmbientHorizontalDiagrams.triLong S d m C X) (AmbientHorizontalDiagrams.triShort S d m C X) (fitted X d m C h)
include h in
theorem original : Triangle S d m C X := unpack X d m C h
end ContextualComposition.GrothendieckStep.AmbientTriangle
