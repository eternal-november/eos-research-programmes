module
public import ContextualComposition.AmbientObserverGlue
public import ContextualComposition.AmbientIsoFragments
public import ContextualComposition.AmbientIsoWords
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientScheduleGlue
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObserverIso
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
open AmbientIsoFragments AmbientObserverRead
variable {n : Nat}
section T
variable (A L R : ContextadHorizontalLaws.Edge (S := S) n) (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
variable {u v w z : obj S n (Eye.{u,v} (B := B)) ⟶ obj S 1 (Eye.{u,v} (B := B))} (a : u ≅ v) (b : v ≅ w) (c : u ≅ w) (j : w ≅ z)
theorem tri (ha : At (Eye.{u,v} (B := B)) A a) (hb : At (Eye.{u,v} (B := B)) L b) (hc : At (Eye.{u,v} (B := B)) R c) (h : AmbientIsoWords.Same (a ≪≫ b ≪≫ j) (c ≪≫ j)) :
    AmbientFragmentGlue.TriGrade A L R s₀ s₁ s₂ :=
  AmbientObserverGlue.tri (n := n) (a := a.hom) (l := b.hom) (q := c.hom) A L R s₀ s₁ s₂ ha hb hc (AmbientIsoWords.triBack a b c j h)
end T
section P
variable (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : A.src = D.src) (s₁ : A.dst = B'.src) (s₂ : B'.dst = C.src) (s₃ : D.dst = J.src) (s₄ : J.dst = E.src) (s₅ : E.dst = C.dst)
variable {u v w z y t : obj S n (Eye.{u,v} (B := B)) ⟶ obj S 1 (Eye.{u,v} (B := B))} (a : u ≅ v) (b : v ≅ w) (c : w ≅ z) (d : u ≅ y) (j : y ≅ t) (e : t ≅ z)
theorem pent (ha : At (Eye.{u,v} (B := B)) A a) (hb : At (Eye.{u,v} (B := B)) B' b) (hc : At (Eye.{u,v} (B := B)) C c) (hd : At (Eye.{u,v} (B := B)) D d) (hj : At (Eye.{u,v} (B := B)) J j) (he : At (Eye.{u,v} (B := B)) E e)
    (h : AmbientIsoWords.Same (a ≪≫ b ≪≫ c) (d ≪≫ j ≪≫ e)) : AmbientFragmentGlue.PentGrade A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅ :=
  AmbientObserverGlue.pent (n := n) (a := a.hom) (b := b.hom) (c := c.hom) (d := d.hom) (j := j.hom) (e := e.hom)
    A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅ ha hb hc hd hj he (AmbientIsoWords.pentBack a b c d j e h)
end P
end ContextualComposition.GrothendieckStep.AmbientObserverIso
