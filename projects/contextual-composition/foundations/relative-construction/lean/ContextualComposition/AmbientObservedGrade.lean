module
public import ContextualComposition.AmbientObserverPaths
public import ContextualComposition.AmbientCanonViaLinks
public import ContextualComposition.AmbientTriangleLinks
public import ContextualComposition.AmbientNativeGradePath
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObservedGrade
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientLetterRead ContextadSchedule ContextadAppendCells ContextadDisjointCut
open AmbientScheduleGlue AmbientScheduleFragment
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
open AmbientCanonViaLinks AmbientNativeGradePath
theorem tri (h : AmbientFragmentGlue.TriGrade (triSwitch d m C) (triLeft d m C) (triRight d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C)) : TriangleLaw d m C :=
  AmbientObserverPaths.tri (triSwitch d m C) (triLeft d m C) (triRight d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C) (longT d m C) (shortT d m C) (eTL d m C) (eTR d m C) h
theorem pent (h : AmbientFragmentGlue.PentGrade (pent1 d m C) (pent2 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (oneTwo d m C) (twoThree d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C)) : PentagonLaw d m C :=
  AmbientObserverPaths.pent (pent1 d m C) (pent2 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (oneTwo d m C) (twoThree d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C) (longP d m C) (shortP d m C) (ePL d m C) (ePR d m C) h
end ContextualComposition.GrothendieckStep.AmbientObservedGrade
