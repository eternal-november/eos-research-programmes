module
public import ContextualComposition.ContextadHorizontalModification
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadCellPasting
open TelescopeSquares NativeAssoc
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {U V : Span (B := B)}
theorem opExt {f g : Operation U V} (e : f.grade = g.grade)
    (h : ∀ x, Aligned (f.leg.app x) (g.leg.app x)) : f = g := by
  obtain ⟨f,p,l⟩ := f; obtain ⟨g,q,k⟩ := g; cases e
  have t : l = k := NatTrans.ext (funext fun x => (h x).eq)
  cases t; rfl
variable {i j k l : Nat}
def castCell {f g : Map S i j} (e : f = g) : Cell f g := e ▸ idCell f
theorem compAssoc (f : Map S i j) (g : Map S j k) (h : Map S k l) :
    comp (comp f g) h = comp f (comp g h) :=
  opExt rfl fun _ => NativeCube.ofEq (Category.assoc ..).symm
theorem inHead (n : Nat) (f : Map S i j) : (inside n f).grade ⋙ (blocks S n j).first = (blocks S n i).first :=
  (blocks S n j).first_assemble ..
theorem inTail (n : Nat) (f : Map S i j) : (inside n f).grade ⋙ (blocks S n j).rest = (blocks S n i).rest ⋙ f.grade :=
  (blocks S n j).rest_assemble ..
theorem inId (n i : Nat) : inside n (identity (S := S) i) = identity (n+i) := by
  apply opExt
  · exact (blocks S n i).ext (inHead n _) (inTail n _)
  · intro x
    apply (ContextadInsideCells.leg n _ x).trans
    have h := Functor.congr_obj (blocks S n i).dest x
    exact (show ∀ {a b : B}, a=b → Aligned (𝟙 a) (𝟙 b) from by intro a b h; subst b; exact Aligned.refl _) h
theorem inComp (n : Nat) (f : Map S i j) (g : Map S j k) :
    comp (inside n f) (inside n g) = inside n (comp f g) := by
  apply opExt
  · apply (blocks S n k).ext
    · exact (congrArg ((inside n f).grade ⋙ ·) (inHead n g)).trans ((inHead n f).trans (inHead n _).symm)
    · exact (congrArg ((inside n f).grade ⋙ ·) (inTail n g)).trans ((congrArg (· ⋙ g.grade) (inTail n f)).trans (inTail n (comp f g)).symm)
  · intro x
    apply Aligned.trans _ (ContextadInsideCells.leg n _ x).symm
    exact ((ContextadInsideCells.leg n g _).trans (ContextadPayloadModification.appChange g.leg (Functor.congr_obj (inTail n f) x))).comp (ContextadInsideCells.leg n f x)
end ContextualComposition.GrothendieckStep.ContextadSchedule
