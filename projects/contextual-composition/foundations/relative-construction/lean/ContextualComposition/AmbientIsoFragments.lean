module
public import ContextualComposition.AmbientIsoWords
public import ContextualComposition.AmbientFragmentGlue
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientScheduleGlue
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientIsoFragments
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
variable {n : Nat} (X : Obj.{u,v} B)
variable (e : ContextadHorizontalLaws.Edge (S := S) n)
variable {a b : obj S n X ⟶ obj S 1 X}
def At (t : a ≅ b) : Prop := Fragment X e t.hom
theorem hom (t : a ≅ b) (h : Fragment X e t.hom) : At X e t := h
variable {U : Obj.{u,v} B} {i j : obj S n X ⟶ U} (q : i ≅ j) (m : U ⟶ obj S 1 X)
theorem whisk (h : Fragment X e (q.hom ▷ m)) : At X e (whiskerRightIso q m) := h
section T
variable (A L R : ContextadHorizontalLaws.Edge (S := S) n) (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
variable {u v w z : obj S n X ⟶ obj S 1 X} (a : u ≅ v) (b : v ≅ w) (c : u ≅ w) (j : w ≅ z)
theorem triangle (ha : At X A a) (hb : At X L b) (hc : At X R c) (h : AmbientFragmentGlue.TriGrade A L R s₀ s₁ s₂) :
    AmbientIsoWords.Same (a ≪≫ b ≪≫ j) (c ≪≫ j) :=
  AmbientIsoWords.triangle a b c j (AmbientFragmentGlue.triangle (X := X) (n := n) (a := a.hom) (l := b.hom) (q := c.hom) A L R s₀ s₁ s₂ ha hb hc h)
end T
section P
variable (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : A.src = D.src) (s₁ : A.dst = B'.src) (s₂ : B'.dst = C.src) (s₃ : D.dst = J.src) (s₄ : J.dst = E.src) (s₅ : E.dst = C.dst)
variable {u v w z y t : obj S n X ⟶ obj S 1 X} (a : u ≅ v) (b : v ≅ w) (c : w ≅ z) (d : u ≅ y) (j : y ≅ t) (e : t ≅ z)
theorem pentagon (ha : At X A a) (hb : At X B' b) (hc : At X C c) (hd : At X D d) (hj : At X J j) (he : At X E e)
  (h : AmbientFragmentGlue.PentGrade A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅) : AmbientIsoWords.Same (a ≪≫ b ≪≫ c) (d ≪≫ j ≪≫ e) :=
  AmbientIsoWords.pentagon a b c d j e (AmbientFragmentGlue.pentagon (X := X) (n := n) (a := a.hom) (b := b.hom) (c := c.hom) (d := d.hom) (j := j.hom) (e := e.hom) A B' C D E J s₀ s₁ s₂ s₃ s₄ s₅ ha hb hc hd hj he h)
end P
end ContextualComposition.GrothendieckStep.AmbientIsoFragments
