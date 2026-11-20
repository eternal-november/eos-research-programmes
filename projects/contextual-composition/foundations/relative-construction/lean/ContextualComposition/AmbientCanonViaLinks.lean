module
public import ContextualComposition.AmbientTriangleLinks
public import ContextualComposition.AmbientNativeGradePath
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCanonViaLinks
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
theorem tri0 : (triRight d m C).src = (triSwitch d m C).src := pushOut (n := 1) (insert S d) (tensor m) (tensor m)
theorem tri1 : (triSwitch d m C).dst = (triLeft d m C).src := pullIn (n := 1) (leftUnit d) (tensor m) (tensor m)
theorem tri2 : (triLeft d m C).dst = (triRight d m C).dst := congrArg (comp · (tensor m)) ((inId (S := S) 1 1).trans (outId 1).symm)
noncomputable def exchangeEdge : ContextadHorizontalLaws.Edge (S := S) 4 := edge (after (disjoint (tensor m) (tensor m) m.cart) (tensor m))
theorem oneTwo : (pent1 d m C).dst = (pent2 d m C).src := pushOut (n := 1) (tensor m) (tensor m) (tensor m)
theorem twoThree : (pent2 d m C).dst = (pent3 d m C).src := pullIn (n := 1) (firstTwo m) (tensor m) (tensor m)
theorem fourX : (pent4 d m C).dst = (exchangeEdge m).src := (compAssoc (suffix (firstTwo m)) (lastTwo m) (tensor m)).symm
theorem xFive : (exchangeEdge m).dst = (pent5 d m C).src := compAssoc (inside 2 (tensor m)) (firstTwo m) (tensor m)

open AmbientNativeGradePath
set_option linter.defProp false in
noncomputable def longT := ContextadHorizontalLaws.triLong d m C (canonicalTriangle d m C)
set_option linter.defProp false in
noncomputable def shortT := ContextadHorizontalLaws.triShort d m C
open AmbientTriangleLinks
theorem instanceLink : canonicalTriangle d m C = byCasts (triRight d m C) (triSwitch d m C) (triLeft d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C) := rfl
theorem literalPath : longT d m C = AmbientTriangleLinks.path (triRight d m C) (triSwitch d m C) (triLeft d m C) (canonicalTriangle d m C) := rfl
set_option linter.defProp false in
def eTL := AmbientTriangleLinks.installed (triRight d m C) (triSwitch d m C) (triLeft d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C) (canonicalTriangle d m C) (longT d m C) (literalPath d m C) (instanceLink d m C)
theorem eTR : shortT d m C = tShort (triRight d m C) := rfl
theorem hT (h : TriangleLaw d m C) : EqualPaths (longT d m C) (shortT d m C) := h
set_option linter.defProp false in
def fromTriangle (h : TriangleLaw d m C) := t (triSwitch d m C) (triLeft d m C) (triRight d m C) (tri0 d m C) (tri1 d m C) (tri2 d m C) (longT d m C) (shortT d m C) (eTL d m C) (eTR d m C) (hT d m C h)
noncomputable def longP := ContextadHorizontalLaws.pentLong d m C (canonicalPentagon d m C)
noncomputable def shortP := ContextadHorizontalLaws.pentShort d m C (canonicalPentagon d m C)
theorem ePL : longP d m C = pLong (pent1 d m C) (pent2 d m C) (pent3 d m C) (oneTwo d m C) (twoThree d m C) := rfl
theorem ePR : shortP d m C = pShort (pent1 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C) := rfl
theorem hP (h : PentagonLaw d m C) : EqualPaths (longP d m C) (shortP d m C) := h
set_option linter.defProp false in
def fromPentagon (h : PentagonLaw d m C) := p (pent1 d m C) (pent2 d m C) (pent3 d m C) (pent4 d m C) (pent5 d m C) (exchangeEdge m) (pentStartRoute d m C) (oneTwo d m C) (twoThree d m C) (fourX d m C) (xFive d m C) (pentEndRoute d m C) (longP d m C) (shortP d m C) (ePL d m C) (ePR d m C) (hP d m C h)
end ContextualComposition.GrothendieckStep.AmbientCanonViaLinks
