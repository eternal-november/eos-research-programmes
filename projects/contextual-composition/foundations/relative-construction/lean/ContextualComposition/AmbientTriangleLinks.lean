module
public import ContextualComposition.AmbientNativeGradePath
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientTriangleLinks
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

open AmbientNativeGradePath
variable {n : Nat} (R A L : ContextadHorizontalLaws.Edge (S := S) n)
def path (z : TriangleLink R A L) : Path R.src R.dst := .more z.start (.more A.cell (.more z.middle (.more L.cell (.one z.finish))))
variable (u : R.src = A.src) (v : A.dst = L.src) (w : L.dst = R.dst)
def byCasts : TriangleLink R A L := ⟨castCell u,castCell v,castCell w⟩
theorem installed (z : TriangleLink R A L) (q : Path R.src R.dst) (h : q = path R A L z) (k : z = byCasts R A L u v w) :
    q = tLong A L R u v w := by subst q; subst z; rfl
end ContextualComposition.GrothendieckStep.AmbientTriangleLinks
