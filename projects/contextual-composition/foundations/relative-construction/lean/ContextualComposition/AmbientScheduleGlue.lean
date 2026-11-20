module
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientScheduleGlue
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
variable {X : Obj.{u,v} B} {i : Nat} {r s : Map S i 1} {a b : obj S i X ⟶ obj S 1 X}
theorem exactRows {v w : a ⟶ b} {c e : Cell r s} (f : Reads v c) (g : Reads w e) (h : ∀ k, c.grade.hom.app k = e.grade.hom.app k) : v = w := by
  cases sameCell (S := S) c e h
  exact extRaw S (fun x => (f x).trans (g x).symm)
section Triangle
variable {n : Nat} (A L R : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : R.src = A.src) (s₁ : A.dst = L.src) (s₂ : L.dst = R.dst)
def line := thenCell (castCell s₀) (thenCell A.cell (thenCell (castCell s₁) (thenCell L.cell (castCell s₂))))
variable {X : Obj.{u,v} B} {u v w : obj S n X ⟶ obj S 1 X} {a : u ⟶ v} {l : v ⟶ w} {q : u ⟶ w}
theorem triangle (ha : Reads a A.cell) (hl : Reads l L.cell) (hr : Reads q R.cell)
    (h : ∀ x, (line A L R s₀ s₁ s₂).grade.hom.app x = R.cell.grade.hom.app x) : a ≫ l = q := by
  exact exactRows (castL s₀ (vertical ha (castL s₁ (castR s₂ hl)))) hr h
end Triangle
section Pentagon
variable {n : Nat} (A B' C D E J : ContextadHorizontalLaws.Edge (S := S) n)
variable (s₀ : A.src = D.src) (s₁ : A.dst = B'.src) (s₂ : B'.dst = C.src) (s₃ : D.dst = J.src) (s₄ : J.dst = E.src) (s₅ : E.dst = C.dst)
def longWord := thenCell A.cell (thenCell (castCell s₁) (thenCell B'.cell (thenCell (castCell s₂) C.cell)))
def shortWord := thenCell (castCell s₀) (thenCell D.cell (thenCell (thenCell (castCell s₃) (thenCell J.cell (castCell s₄))) (thenCell E.cell (castCell s₅))))
variable {X : Obj.{u,v} B} {u v w z y t : obj S n X ⟶ obj S 1 X} {a : u ⟶ v} {b : v ⟶ w} {c : w ⟶ z} {d : u ⟶ y} {j : y ⟶ t} {e : t ⟶ z}
theorem pentagon (ha : Reads a A.cell) (hb : Reads b B'.cell) (hc : Reads c C.cell) (hd : Reads d D.cell) (hj : Reads j J.cell) (he : Reads e E.cell)
    (h : ∀ x, (longWord A B' C s₁ s₂).grade.hom.app x = (shortWord A C D E J s₀ s₃ s₄ s₅).grade.hom.app x) :
    a ≫ b ≫ c = d ≫ j ≫ e := by
  exact exactRows (vertical ha (castL s₁ (vertical hb (castL s₂ hc))))
    (castL s₀ (vertical hd (vertical (castL s₃ (castR s₄ hj)) (castR s₅ he)))) h
end Pentagon
end ContextualComposition.GrothendieckStep.AmbientScheduleGlue
