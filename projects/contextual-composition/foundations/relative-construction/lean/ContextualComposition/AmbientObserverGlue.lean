module
public import ContextualComposition.AmbientObserverRead
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientScheduleGlue
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObserverGlue
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
open AmbientScheduleFragment AmbientScheduleGlue AmbientObserverRead AmbientFragmentGlue
section Triangle
variable {n : Nat} (A L R : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
variable {u v w : obj S n (Eye.{u,v} (B := B)) ⟶ obj S 1 (Eye.{u,v} (B := B))} {a : u ⟶ v} {l : v ⟶ w} {q : u ⟶ w}
theorem tri (ha : Fragment (Eye (B := B)) A a) (hl : Fragment (Eye (B := B)) L l) (hr : Fragment (Eye (B := B)) R q) (eq : a ≫ l = q) :
    TriGrade A L R s₀ s₁ s₂ := detect (c := line A L R s₀ s₁ s₂) (e := R.cell) (castL s₀ (vertical ha (castL s₁ (castR s₂ hl)))) hr eq
end Triangle
section Pentagon
variable {n : Nat} (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : A.src = D.src) (s₁ : A.dst = B'.src) (s₂ : B'.dst = C.src) (s₃ : D.dst = J.src) (s₄ : J.dst = E.src) (s₅ : E.dst = C.dst)
variable {u v w z y t : obj S n (Eye.{u,v} (B := B)) ⟶ obj S 1 (Eye.{u,v} (B := B))}
variable {a : u ⟶ v} {b : v ⟶ w} {c : w ⟶ z} {d : u ⟶ y} {j : y ⟶ t} {e : t ⟶ z}
theorem pent (ha : Fragment (Eye (B := B)) A a) (hb : Fragment (Eye (B := B)) B' b) (hc : Fragment (Eye (B := B)) C c) (hd : Fragment (Eye (B := B)) D d) (hj : Fragment (Eye (B := B)) J j) (he : Fragment (Eye (B := B)) E e)
    (eq : a ≫ b ≫ c = d ≫ j ≫ e) : PentGrade A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅ :=
  detect (c := longWord A B' C s₁ s₂) (e := shortWord A C D E J s₀ s₃ s₄ s₅)
    (vertical ha (castL s₁ (vertical hb (castL s₂ hc)))) (castL s₀ (vertical hd (vertical (castL s₃ (castR s₄ hj)) (castR s₅ he)))) eq
end Pentagon
end ContextualComposition.GrothendieckStep.AmbientObserverGlue
