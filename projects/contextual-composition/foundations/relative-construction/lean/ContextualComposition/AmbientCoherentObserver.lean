module
public import ContextualComposition.AmbientTriangle
public import ContextualComposition.AmbientPentagon
public import ContextualComposition.AmbientObserverIso
public import ContextualComposition.AmbientObservedGrade
public import ContextualComposition.AmbientCoherentPseudomonad
public import ContextualComposition.AmbientActualIsoEdges
public import ContextualComposition.AmbientCanonViaLinks
public import ContextualComposition.AmbientScheduleEdges
public import ContextualComposition.AmbientFoldedAssocRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCoherentObserver
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
open AmbientObserverRead
section TriangleReflection
variable (h : Triangle S d m C (Eye.{u,v} (B := B)))
set_option linter.defProp false in
def inputTriangle := AmbientIsoWords.ofHom (AmbientHorizontalDiagrams.triLong S d m C (Eye.{u,v} (B := B))) (AmbientHorizontalDiagrams.triShort S d m C (Eye.{u,v} (B := B))) h
set_option linter.defProp false in
def alignedTriangle := faces (AmbientHorizontalDiagrams.triLong S d m C (Eye.{u,v} (B := B))) (AmbientHorizontalDiagrams.triShort S d m C (Eye.{u,v} (B := B))) (AmbientTriangle.long (Eye.{u,v} (B := B)) d m C) (AmbientTriangle.short (Eye.{u,v} (B := B)) d m C)
  (AmbientTriangle.leftFrame (Eye.{u,v} (B := B)) d m C).symm (AmbientTriangle.rightFrame (Eye.{u,v} (B := B)) d m C).symm (inputTriangle d m C h)
set_option linter.defProp false in
def rawTriangle := AmbientObserverIso.tri (n := 2) (triSwitch d m C) (triLeft d m C) (triRight d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C)
  (TA (Eye.{u,v} (B := B)) d m C) (TL (Eye.{u,v} (B := B)) d m C) (TR (Eye.{u,v} (B := B)) d m C) (λ_ _)
  (rTA (Eye.{u,v} (B := B)) d m C) (rTL (Eye.{u,v} (B := B)) d m C) (rTR (Eye.{u,v} (B := B)) d m C) (alignedTriangle d m C h)

theorem triIff : Triangle S d m C (Eye.{u,v} (B := B)) ↔ TriangleLaw d m C :=
  ⟨fun k => AmbientObservedGrade.tri d m C (rawTriangle d m C k),fun k => AmbientTriangle.original (Eye.{u,v} (B := B)) d m C k⟩
end TriangleReflection
section PentagonReflection
variable (h : Pentagon S d m C (Eye.{u,v} (B := B)))
set_option linter.defProp false in
def inputPentagon := AmbientIsoWords.ofHom (AmbientHorizontalDiagrams.pentLong S d m C (Eye.{u,v} (B := B))) (AmbientHorizontalDiagrams.pentShort S d m C (Eye.{u,v} (B := B))) h
set_option linter.defProp false in
def alignedPentagon := faces (AmbientHorizontalDiagrams.pentLong S d m C (Eye.{u,v} (B := B))) (AmbientHorizontalDiagrams.pentShort S d m C (Eye.{u,v} (B := B))) (AmbientPentagon.long (Eye.{u,v} (B := B)) d m C) (AmbientPentagon.short (Eye.{u,v} (B := B)) d m C)
  (AmbientPentagon.leftFrame (Eye.{u,v} (B := B)) d m C).symm (AmbientPentagon.rightFrame (Eye.{u,v} (B := B)) d m C).symm (inputPentagon d m C h)
set_option linter.defProp false in
def rawPentagon := AmbientObserverIso.pent (n := 4) (pent1 d m C) (pent2 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (oneTwo d m C) (twoThree d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C)
  (PA (Eye.{u,v} (B := B)) d m C) (PB (Eye.{u,v} (B := B)) d m C) (PC (Eye.{u,v} (B := B)) d m C) (PD (Eye.{u,v} (B := B)) d m C) (PJ (Eye.{u,v} (B := B)) m) (PE (Eye.{u,v} (B := B)) d m C) 
  (rPA (Eye.{u,v} (B := B)) d m C) (rPB (Eye.{u,v} (B := B)) d m C) (rPC (Eye.{u,v} (B := B)) d m C) (rPD (Eye.{u,v} (B := B)) d m C) (rPJ (Eye.{u,v} (B := B)) m) (rPE (Eye.{u,v} (B := B)) d m C) (alignedPentagon d m C h)

theorem pentIff : Pentagon S d m C (Eye.{u,v} (B := B)) ↔ PentagonLaw d m C :=
  ⟨fun k => AmbientObservedGrade.pent d m C (rawPentagon d m C k),fun k => AmbientPentagon.original (Eye.{u,v} (B := B)) d m C k⟩
end PentagonReflection
theorem exactCriterion : Coherent d m C ↔ AmbientCoherentPseudomonad.Laws S d m C := by
  constructor
  · exact fun h => (AmbientCoherentPseudomonad.build d m C h).laws
  · exact fun h => ⟨(triIff d m C).mp (h.triangle _),(pentIff d m C).mp (h.pentagon _)⟩
end ContextualComposition.GrothendieckStep.AmbientCoherentObserver
