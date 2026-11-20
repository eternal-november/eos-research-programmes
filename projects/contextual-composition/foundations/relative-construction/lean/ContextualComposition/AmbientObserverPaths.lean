module
public import ContextualComposition.AmbientNativeGradePath
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObserverPaths
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
variable {n : Nat} (A L R : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
theorem tri (a b : Path R.src R.dst) (e : a = tLong A L R s₀ s₁ s₂) (w : b = tShort R)
    (h : AmbientFragmentGlue.TriGrade A L R s₀ s₁ s₂) : EqualPaths a b := by subst a; subst b; exact h
section P
variable (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (a : A.src = D.src) (b : A.dst = B'.src) (c : B'.dst = C.src) (d : D.dst = J.src) (e : J.dst = E.src) (f : E.dst = C.dst)
theorem pent (l q : Path A.src C.dst) (el : l = pLong A B' C b c) (er : q = pShort A C D E J a d e f)
    (h : AmbientFragmentGlue.PentGrade A B' C D E J a b c d e f) : EqualPaths l q := by subst l; subst q; exact h
end P
end ContextualComposition.GrothendieckStep.AmbientObserverPaths
