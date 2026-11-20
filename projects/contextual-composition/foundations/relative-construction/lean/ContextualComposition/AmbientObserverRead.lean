module
public import ContextualComposition.AmbientScheduleGlue
public import ContextualComposition.AmbientScheduleRealization
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObserverRead
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
open AmbientScheduleGlue
noncomputable abbrev Eye := (ContextadScheduleDetection.observer B : Obj.{u,v} B)
variable {i j : Nat} {r s : Map S i j} {a b : obj S i (Eye (B := B)) ⟶ obj S j (Eye (B := B))}
variable {t n : a ⟶ b} {c e : Cell r s}
theorem detect (h : Reads (S := S) (X := Eye (B := B)) (j := i) (k := j) t c) (w : Reads (S := S) (X := Eye (B := B)) (j := i) (k := j) n e) (eq : t = n) :
    ∀ k, c.grade.hom.app k = e.grade.hom.app k := by
  subst n; intro k
  let X := Eye.{u,v} (B := B)
  let z : Raw S X i := pair (underlying X) (power S i).dest k ((power S i).dest.obj k)
  have d := ((h z).symm.trans (w z)).eq
  exact (ContextadCellWhisker.readGrade c X z).symm.trans ((congrArg gradeMap d).trans (ContextadCellWhisker.readGrade e X z))
end ContextualComposition.GrothendieckStep.AmbientObserverRead
