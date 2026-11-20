module
public import ContextualComposition.AmbientHorizontalFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientHorizontalRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X : Obj.{u,v} B} {i j k l : Nat} {r s t : Map S j k}
abbrev Reads {u v : obj S j X ⟶ obj S k X} (a : u ⟶ v) (c : Cell r s) :=
  ∀ x, Aligned (atRaw S a x) ((rawCell (underlying X) c).hom.app x)
theorem vertical {u v w : obj S j X ⟶ obj S k X} {a : u ⟶ v} {b : v ⟶ w} {c : Cell r s} {d : Cell s t}
    (h : Reads a c) (k : Reads b d) : Reads (a ≫ b) (thenCell c d) := by
  intro x; rw [compAt]; exact ((h x).comp (k x)).trans (NativeCube.ofEq (NatTrans.congr_app (rawComp (underlying X) c d) x)).symm
theorem cmp (c : Cell r s) (p : gradeCart r) (q : gradeCart s) : Reads (AmbientNativeModification.cmp c p q X).hom c :=
  fun x => AmbientNativeModification.cmpAt c p q x
theorem whiskSquare {D E : Type*} [Category* D] [Category* E] {F G H J : D ⥤ E} (a : F ⟶ G) (b : H ⟶ J)
    (l : F = H) (r : G = J) (h : a ≫ eqToHom r = eqToHom l ≫ b) (x : D) : Aligned (a.app x) (b.app x) := by
  subst H; subst J; simp at h; exact NativeCube.ofEq (NatTrans.congr_app h x)
theorem pre {f g : obj S j X ⟶ obj S k X} {a : f ⟶ g} {c : Cell r s} (h : Reads a c)
    (v : obj S i X ⟶ obj S j X) (p : Map S i j) (e : encode S v = raw (underlying X) p) : Reads (v ◁ a) (before c p) := by
  intro x
  apply (preAt S v a x).trans
  apply (h _).trans
  apply (ContextadPayloadModification.appChange (rawCell X c).hom (Functor.congr_obj e x)).trans
  exact (whiskSquare _ _ _ _ (beforeSquare c X p) x).symm
theorem post {f g : obj S j X ⟶ obj S k X} {a : f ⟶ g} {c : Cell r s} (h : Reads a c)
    (v : obj S k X ⟶ obj S l X) (p : Map S k l) (e : encode S v = raw (underlying X) p) : Reads (a ▷ v) (after c p) := by
  intro x
  apply (postAt S a v x).trans
  apply (NativeCube.functorAlign e _).trans
  apply ((h x).map (raw X p)).trans
  exact (whiskSquare _ _ _ _ (afterSquare c X p) x).symm
end ContextualComposition.GrothendieckStep.AmbientHorizontalRead
