module
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNativeGradePath
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

variable {n : Nat} {r s : Map S n 1}
def EqualCells (a b : Cell r s) : Prop := ∀ x, a.grade.hom.app x = b.grade.hom.app x
def EqualPaths (a b : Path r s) : Prop := EqualCells (composite a) (composite b)
theorem pass (a b : Path r s) (c d : Cell r s) (e : composite a = c) (w : composite b = d) (h : EqualPaths a b) : EqualCells c d := by
  subst c; subst d; exact h
variable (A L R : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
def tLong : Path R.src R.dst := .more (castCell s₀) (.more A.cell (.more (castCell s₁) (.more L.cell (.one (castCell s₂)))))
def tShort : Path R.src R.dst := .one R.cell
theorem t (a b : Path R.src R.dst) (e : a = tLong A L R s₀ s₁ s₂) (w : b = tShort R)
  (h : EqualPaths a b) : AmbientFragmentGlue.TriGrade A L R s₀ s₁ s₂ := by
  subst a; subst b
  exact pass (tLong A L R s₀ s₁ s₂) (tShort R) (line A L R s₀ s₁ s₂) R.cell rfl rfl h
section P
variable (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (a : A.src = D.src) (b : A.dst = B'.src) (c : B'.dst = C.src) (d : D.dst = J.src) (e : J.dst = E.src) (f : E.dst = C.dst)
def pLong : Path A.src C.dst := .more A.cell (.more (castCell b) (.more B'.cell (.more (castCell c) (.one C.cell))))
def pShort : Path A.src C.dst := .more (castCell a) (.more D.cell (.more (thenCell (castCell d) (thenCell J.cell (castCell e))) (.more E.cell (.one (castCell f)))))
theorem p (l q : Path A.src C.dst) (el : l = pLong A B' C b c) (er : q = pShort A C D E J a d e f)
  (h : EqualPaths l q) : AmbientFragmentGlue.PentGrade A B' C D E J a b c d e f := by
  subst l; subst q
  exact pass (pLong A B' C b c) (pShort A C D E J a d e f) (longWord A B' C b c) (shortWord A C D E J a d e f) rfl rfl h
end P
end ContextualComposition.GrothendieckStep.AmbientNativeGradePath
