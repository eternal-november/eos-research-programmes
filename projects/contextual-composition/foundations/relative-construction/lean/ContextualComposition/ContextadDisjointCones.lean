module
public import ContextualComposition.ContextadDisjointCut
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadDisjointCut
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadSchedule ContextadLawTransport
open TelescopeSquares NativeAssoc FibreValue NativeTrace NativeCleavage
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (f g : Map S 2 1)
noncomputable abbrev leftCone : (lhs f g).grade ⋙ last S 1 ⟶ leaf₂ S ⋙ g.grade :=
  eqToHom (leftTail f g) ≫ whiskerRight (move f) g.grade
def pullCone {A D E F : Type*} [Category* A] [Category* D] [Category* E] [Category* F] (a : A ⥤ D) (b : D ⥤ E)
    (c : E ⥤ F) (d : D ⥤ F) (t : A ⥤ F) (l : b ⋙ c ⟶ d) (h : a ⋙ d = t) :
    (a ⋙ b) ⋙ c ⟶ t := ContextadOuterCharts.joinRight a b c d l ≫ eqToHom h
noncomputable def preSnoc {n i j : Nat} (f : Map S i j) (a : Map S n (i+1))
    (t : (power S n).apex ⥤ Apex P) (h : a.grade ⋙ last S i = t) :
    (comp a (suffix f)).grade ⋙ last S j ⟶ t :=
  pullCone a.grade (suffix f).grade (last S j) (last S i) t (snocArrow f) h
theorem preSnocTip {n i j : Nat} (f : Map S i j) (a : Map S n (i+1))
    (t : (power S n).apex ⥤ Apex P) (h : a.grade ⋙ last S i = t) (x : (power S n).apex) :
    Aligned ((preSnoc f a t h).app x) ((snocArrow f).app (a.grade.obj x)) := by
  simpa only [preSnoc,pullCone,ContextadOuterCharts.joinRight,NatTrans.comp_app,whiskerLeft_app,eqToHom_app] using
    Aligned.trailing ((snocArrow f).app (a.grade.obj x)) (Functor.congr_obj h x)
noncomputable def rightCone : (rhs f g).grade ⋙ last S 1 ⟶ leaf₂ S ⋙ g.grade :=
  preSnoc (S := S) (n := 4) (i := 2) (j := 1) f (inside 2 g) (leaf₂ S ⋙ g.grade) (rightTail g)
theorem leftTip (x) : Aligned ((leftCone f g).app x) (g.grade.map ((move f).app x)) := by
  simpa only [eqToHom_refl,Category.comp_id,leftCone,whiskerRight_app] using ContextadOuterCharts.castApp (leftTail f g) rfl (whiskerRight (move f) g.grade) x
theorem rightTip (x) : Aligned ((rightCone f g).app x) ((snocArrow (S := S) (i := 2) (j := 1) f).app ((inside (S := S) (i := 2) (j := 1) 2 g).grade.obj x)) :=
  preSnocTip (S := S) (n := 4) (i := 2) (j := 1) f (inside 2 g) (leaf₂ S ⋙ g.grade) (rightTail g) x
end ContextualComposition.GrothendieckStep.ContextadDisjointCut
