module
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientScheduleGlue
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFragmentGlue
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
open AmbientScheduleFragment AmbientScheduleGlue
section Triangle
variable {n : Nat} (A L R : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
def TriGrade : Prop := ∀ x, (line A L R s₀ s₁ s₂).grade.hom.app x = R.cell.grade.hom.app x
variable {X : Obj.{u,v} B} {u v w : obj S n X ⟶ obj S 1 X} {a : u ⟶ v} {l : v ⟶ w} {q : u ⟶ w}
theorem triangle (ha : Fragment X A a) (hl : Fragment X L l) (hr : Fragment X R q)
    (h : TriGrade A L R s₀ s₁ s₂) : a ≫ l = q := AmbientScheduleGlue.triangle (X := X) (n := n) (a := a) (l := l) (q := q) A L R s₀ s₁ s₂ ha hl hr h
end Triangle
section Pentagon
variable {n : Nat} (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : A.src = D.src) (s₁ : A.dst = B'.src) (s₂ : B'.dst = C.src) (s₃ : D.dst = J.src) (s₄ : J.dst = E.src) (s₅ : E.dst = C.dst)
def PentGrade : Prop := ∀ x, (longWord A B' C s₁ s₂).grade.hom.app x = (shortWord A C D E J s₀ s₃ s₄ s₅).grade.hom.app x
variable {X : Obj.{u,v} B} {u v w z y t : obj S n X ⟶ obj S 1 X} {a : u ⟶ v} {b : v ⟶ w} {c : w ⟶ z} {d : u ⟶ y} {j : y ⟶ t} {e : t ⟶ z}
theorem pentagon (ha : Fragment X A a) (hb : Fragment X B' b) (hc : Fragment X C c) (hd : Fragment X D d) (hj : Fragment X J j) (he : Fragment X E e)
    (h : PentGrade A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅) : a ≫ b ≫ c = d ≫ j ≫ e :=
  AmbientScheduleGlue.pentagon (X := X) (n := n) (a := a) (b := b) (c := c) (d := d) (j := j) (e := e) A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅ ha hb hc hd hj he h
end Pentagon
end ContextualComposition.GrothendieckStep.AmbientFragmentGlue
