module
public import ContextualComposition.TelescopeAmbientBase
public import ContextualComposition.TelescopeAmbientComponents

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientLeaf

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open NativeCleavage NativeBlocks SpanApex CoproductSpan CoproductSpan.All
open FibreValue TelescopeSquares ContextadAmbientPayload AmbientBicategory AmbientCoordinates
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v

private theorem pureBefore {C : Type*} [Category* C] {x y z : C}
    (q : x ⟶ y) (r : y ⟶ z) (hq : Pure q) : Aligned (q ≫ r) r := by
  obtain ⟨rfl,rfl⟩ := hq
  exact NativeCube.ofEq (Category.id_comp r)

/-- The actual strong naturality cell factors the image of the chosen value lift. -/
theorem naturality_lift {B : Type u} [Category.{v} B] {V W : Bᵒᵖ ⥤ Cat.{v,u}}
    (m : StrongTrans V.toPseudofunctor' W.toPseudofunctor') {A D : B} (a : A ⟶ D) (x : V.obj (op D)) :
    Aligned ((incl W A).map ((m.naturality a.op.toLoc).hom.toNatTrans.app x) ≫
      FibreValue.arrow W a ((AmbientRoundTrip.compAt m D).obj x))
      ((totalStrong m).map (FibreValue.arrow V a x)) := by
  let j := ContextadModification.decodedStrong V W (totalStrong m) (strongOver m) (strongCart m)
  have h : Aligned ((incl W A).map ((j.naturality a.op.toLoc).hom.toNatTrans.app x) ≫
      FibreValue.arrow W a ((AmbientRoundTrip.compAt j D).obj x))
      ((totalStrong m).map (FibreValue.arrow V a x)) :=
    AmbientDescentRecognition.decodedFac V W (strongOver m) (strongCart m) a x
  rw [show j = m from AmbientRoundTrip.decodeEncode m] at h
  exact h

variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (X : Obj.{u,v} B) {A D : B} (a : A ⟶ D)

noncomputable abbrev chosen (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :=
  Reindex.lift (extendChoice (underlying X) (dst S n) (src S n) (SpanPull.All.parts S n)) a
    ((FibreTotal.into (underlying X) (dst S n) (src S n) D).obj x)

/-- The actual zero-length base comparison factors the selected raw lift. -/
theorem zero_base_lift (x : Total (underlying X) (leg (src S) (dst S) D 0)) :
    Aligned ((incl (underlying X) A).map ((SumChange.componentBase S (underlying X) a 0).hom.app x) ≫
      FibreValue.arrow (underlying X) a ((component S (underlying X) D 0).functor.obj x))
      (chosen S X a 0 x) := by
  let t := (FibreTotal.into (underlying X) (𝟭 B) (𝟭 B) D).obj x
  let k := (FibreValue.valueSquare (underlying X) a).hom.app t
  apply (pureBefore _ _ (pureMap (incl (underlying X) A) (show Pure k from ⟨_,valueApp _ _ _⟩))).trans
  exact (AmbientDescentRecognition.chosen (underlying X) a t).symm

set_option linter.defProp false in
/-- The chosen positive evaluation face at the strict-fibre image of the actual presented object. -/
def successor_fibre_lift (n : Nat)
    (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :=
  (NativeCube.evaluation S (underlying X) n a).fac
    ((FibreTotal.into (underlying X) (positivePowers P S n).dest (positivePowers P S n).source D).obj x)

variable {X} {Y : Obj.{u,v} B} (f : X ⟶ Y)

private theorem chosenAtEq {V L : Type*} [Category* V] [Category* L] {p : L ⥤ V}
    (c : Cleavage p) {A D : V} (a : A ⟶ D) {x y : p.Fiber D} (h : x = y) :
    Aligned (Reindex.lift c a x) (Reindex.lift c a y) := by
  subst y
  exact Aligned.refl _

/-- The presented strong/base cell, included back into the raw total category, factors the
image of the chosen lift at the original length and endpoints. -/
theorem presented_lift (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :
    Aligned ((SpanPayload.Power.fibreInclude A (underlying Y) (src S n) (dst S n)).map
        ((TelescopeAmbientBase.presented f.hom (dst S n) (src S n) (SpanPull.All.parts S n) a).hom.app x) ≫
      chosen S Y a n ((atEndpoint f.hom (leg (src S) (dst S) D n)).obj x))
      ((atEndpoint f.hom (dst S n)).map (chosen S X a n x)) := by
  let e := dst S n
  let p := src S n
  let c := SpanPull.All.parts S n
  let y := (FibreTotal.into (underlying X) e p D).obj x
  let F := TelescopeAmbientBase.cartesianFace f.hom e p c a
  have h : Aligned ((SpanPayload.Power.fibreInclude A (underlying Y) p e).map
      ((TelescopeAmbientBase.presented f.hom e p c a).hom.app x)) (F.sq.hom.app y).val :=
    (TelescopeAmbientBase.presented_component f.hom e p c a x).map _
  exact (h.comp (chosenAtEq (extendChoice (underlying Y) e p c) a
    (Functor.congr_obj (TelescopeAmbientBase.intoSquare f.hom e p D) x))).trans (F.fac y)

end ContextualComposition.GrothendieckStep.TelescopeAmbientLeaf
