module
public import ContextualComposition.TelescopePositiveBase
public import ContextualComposition.TelescopePresentationPasting
public import ContextualComposition.AmbientChartRows

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeLeafCancellation
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open NativeCleavage NativeBlocks SpanApex CoproductSpan CoproductSpan.All TelescopeSquares
open ContextadAmbientPayload AmbientBicategory AmbientCoordinates AmbientRoundTrip FibreValue
open TelescopeAmbientComponents TelescopeAmbientMixed SumChange TaggedMixed
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v

/-- Paste two factored arrows before comparing their common cartesian lift. -/
theorem factor_path {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : C ⥤ E) (F : D ⥤ E) {x y z : C} {w : E} {g h k s t : D}
    (j : x ⟶ y) (l : y ⟶ z) (tail : I.obj z ⟶ w) (p : g ⟶ h) (q : h ⟶ k) (result : s ⟶ t)
    (first : Aligned (I.map j) (F.map p)) (second : Aligned (I.map l ≫ tail) (F.map q))
    (fac : Aligned (p ≫ q) result) : Aligned (I.map (j ≫ l) ≫ tail) (F.map result) := by
  rw [Functor.map_comp,Category.assoc]
  exact (first.comp second).trans ((NativeCube.ofEq (F.map_comp p q).symm).trans (fac.map F))

private theorem reflect_alignment {C D : Type*} [Category* C] [Category* D] (I : C ⥤ D) [I.Faithful]
    (inj : Function.Injective I.obj) {x y x' y' : C} {l : x ⟶ y} {r : x' ⟶ y'} (h : Aligned (I.map l) (I.map r)) :
    Aligned l r := by
  obtain rfl : x = x' := inj h.src
  obtain rfl : y = y' := inj h.dst
  exact NativeCube.ofEq (I.map_injective h.eq)

section Cancellation
variable {B : Type u} [Category.{v} B] (H : Bᵒᵖ ⥤ Cat.{v,u}) {A D : B} (a : A ⟶ D)
private theorem align_arrow {x y : H.obj (op D)} (h : x = y) :
    Aligned (FibreValue.arrow H a x) (FibreValue.arrow H a y) := by subst y; exact Aligned.refl _

theorem cancel_value {x y : H.obj (op A)} {z z' : H.obj (op D)}
    (l : x ⟶ (H.map a.op).toFunctor.obj z) (r : y ⟶ (H.map a.op).toFunctor.obj z') (equal : z = z')
    (sq : Aligned ((incl H A).map l ≫ FibreValue.arrow H a z) ((incl H A).map r ≫ FibreValue.arrow H a z')) :
    Aligned l r := by
  let I := incl H A
  let _ : I.Faithful := (inferInstance : (embed H A ⋙ Functor.Fiber.fiberInclusion).Faithful)
  have inj : Function.Injective I.obj := by
    intro p q e
    let pairData : Total H (𝟭 B) → Σ i, H.obj (op i) := fun z => ⟨grade H (𝟭 B) z,payload H (𝟭 B) z⟩
    exact (Sigma.mk.inj_iff.mp (congrArg pairData e)).2.eq
  have over : Aligned ((proj H).map (I.map l)) ((proj H).map (I.map r)) := Aligned.refl _
  exact reflect_alignment I inj (AmbientChartRows.alignCancel (proj H) ((FibreValue.cone H a).cart z) over
    (align_arrow H a equal) sq)

private theorem transport_edges {C : Type*} [Category* C] {x y z w : C} (l : x ⟶ y) (r : z ⟶ w)
    {i : x ⟶ z} {j : y ⟶ w} (aligned : Aligned l r) (hi : ForwardMixed.IsTransport i) (hj : ForwardMixed.IsTransport j) :
    l ≫ j = i ≫ r := by
  obtain ⟨ei,rfl⟩ := hi
  obtain ⟨ej,rfl⟩ := hj
  exact aligned.comm
end Cancellation

variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) {X Y : Obj.{u,v} B} (f : X ⟶ Y) {A D : B} (a : A ⟶ D)

def BaseFactor (V : Obj.{u,v} B) (n : Nat) : Prop :=
  ∀ x : Total (underlying V) (leg (src S) (dst S) D n),
    Aligned ((incl (PackedFree.pow S (underlying V) n) A).map ((componentBase S (underlying V) a n).hom.app x) ≫
      FibreValue.arrow (PackedFree.pow S (underlying V) n) a ((component S (underlying V) D n).functor.obj x))
      ((chart S V n).map (TelescopeAmbientLeaf.chosen S V a n x))

noncomputable abbrev leftPath (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :=
  (component S (underlying Y) A n).functor.map ((nativeLeaf S f a n).hom.app x) ≫
    (componentBase S (underlying Y) a n).hom.app ((weighted S f D n).obj x)

noncomputable abbrev rightPath (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :=
  (target S A f n).map ((componentBase S (underlying X) a n).hom.app x) ≫
    (iterateLeaf S f a n).hom.app ((component S (underlying X) D n).functor.obj x)

set_option linter.defProp false in
def first_alignment (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) D n)) :=
  let s := (nativeLeaf S f a n).hom.app x
  let i := SpanPayload.Power.fibreInclude A (underlying Y) (src S n) (dst S n)
  (NativeCube.functorAlign (component_incl S A (underlying Y) n) s).trans
    ((TelescopePresentationPasting.leaf_alignment S f a n x).map (i ⋙ chart S Y n))

set_option maxHeartbeats 1400000 in
theorem left_factor (n : Nat) (hy : BaseFactor S a Y n) (x : Total (underlying X) (leg (src S) (dst S) D n)) :
    Aligned ((incl (PackedFree.pow S (underlying Y) n) A).map (leftPath S f a n x) ≫
      FibreValue.arrow (PackedFree.pow S (underlying Y) n) a ((component S (underlying Y) D n).functor.obj ((weighted S f D n).obj x)))
      ((chart S Y n).map ((atEndpoint f.hom (dst S n)).map (TelescopeAmbientLeaf.chosen S X a n x))) := by
  let T := PackedFree.pow S (underlying Y) n
  let I := incl T A
  let F := chart S Y n
  let z := (weighted S f D n).obj x
  let base := (nativeLeaf S f a n).hom.app x
  let original := (TelescopeAmbientBase.presented f.hom (dst S n) (src S n) (SpanPull.All.parts S n) a).hom.app x
  let i := SpanPayload.Power.fibreInclude A (underlying Y) (src S n) (dst S n)
  let j := (component S (underlying Y) A n).functor.map base
  let l := (componentBase S (underlying Y) a n).hom.app z
  let tail := FibreValue.arrow T a ((component S (underlying Y) D n).functor.obj z)
  let pa := i.map original
  let qa := TelescopeAmbientLeaf.chosen S Y a n z
  let out := (atEndpoint f.hom (dst S n)).map (TelescopeAmbientLeaf.chosen S X a n x)
  refine factor_path I F
    (x := (AmbientCellTrace.edge j).src) (y := (AmbientCellTrace.edge j).dst) (z := (AmbientCellTrace.edge l).dst)
    (w := (AmbientCellTrace.edge tail).dst) (g := (AmbientCellTrace.edge pa).src) (h := (AmbientCellTrace.edge pa).dst)
    (k := (AmbientCellTrace.edge qa).dst) (s := (AmbientCellTrace.edge out).src) (t := (AmbientCellTrace.edge out).dst)
    j l tail pa qa out ?_ ?_ ?_
  · have h := first_alignment S f a n x
    dsimp only [I, j, F, pa, i, base, original, AmbientCellTrace.edge, Functor.comp_map, Functor.comp_obj,
      SpanPayload.Power.fibreInclude] at h ⊢
    exact h
  · have h := hy z
    dsimp only [I, l, tail, F, qa, T, z, AmbientCellTrace.edge, Functor.comp_obj, Functor.comp_map,
      AmbientCoordinates.chart, TelescopeAmbientMixed.weighted, FibreValue.proj, Evaluation.iterateChoice,
      FibreValue.choice] at h ⊢
    exact h
  · have h := TelescopeAmbientLeaf.presented_lift S a f n x
    dsimp only [pa, qa, out, i, original, z, AmbientCellTrace.edge, TelescopeAmbientMixed.weighted,
      Functor.comp_obj, Functor.comp_map, SpanPayload.Power.fibreInclude] at h ⊢
    exact h

set_option maxHeartbeats 650000 in
theorem right_factor (n : Nat) (hx : BaseFactor S a X n) (x : Total (underlying X) (leg (src S) (dst S) D n)) :
    Aligned ((incl (PackedFree.pow S (underlying Y) n) A).map (rightPath S f a n x) ≫
      FibreValue.arrow (PackedFree.pow S (underlying Y) n) a ((target S D f n).obj ((component S (underlying X) D n).functor.obj x)))
      ((totalStrong (AmbientBicategory.map S n f).hom).map ((chart S X n).map (TelescopeAmbientLeaf.chosen S X a n x))) := by
  let H := PackedFree.pow S (underlying Y) n
  let K := PackedFree.pow S (underlying X) n
  let I := incl H A
  let m := (AmbientBicategory.map S n f).hom
  let F := totalStrong m
  let z := (component S (underlying X) D n).functor.obj x
  let start := (componentBase S (underlying X) a n).hom.app x
  let j := (target S A f n).map start
  let l := (iterateLeaf S f a n).hom.app z
  let tail := FibreValue.arrow H a ((target S D f n).obj z)
  let pa := (incl K A).map start
  let qa := FibreValue.arrow K a z
  let out := (chart S X n).map (TelescopeAmbientLeaf.chosen S X a n x)
  exact factor_path I F
    (x := (AmbientCellTrace.edge j).src) (y := (AmbientCellTrace.edge j).dst) (z := (AmbientCellTrace.edge l).dst)
    (w := (AmbientCellTrace.edge tail).dst) (g := (AmbientCellTrace.edge pa).src) (h := (AmbientCellTrace.edge pa).dst)
    (k := (AmbientCellTrace.edge qa).dst) (s := (AmbientCellTrace.edge out).src) (t := (AmbientCellTrace.edge out).dst)
    j l tail pa qa out (NativeCube.functorAlign (strongIncl m A) start)
      (TelescopeAmbientLeaf.naturality_lift m a z) (hx x)

set_option maxHeartbeats 450000 in
theorem leaf_of_factors (n : Nat) (hx : BaseFactor S a X n) (hy : BaseFactor S a Y n) :
    Cube.Law (TelescopeAmbientMixed.leafMap S f a n) := by
  intro x
  let H := PackedFree.pow S (underlying Y) n
  let k := TelescopeAmbientLeaf.chosen S X a n x
  have h := (left_factor S f a n hy x).trans
    ((NativeCube.functorAlign (AmbientInsideMate.chartAction (S := S) (X := X) (Y := Y) f n) k).trans
       (right_factor S f a n hx x).symm)
  have aligned := cancel_value H a (leftPath S f a n x) (rightPath S f a n x)
    (Functor.congr_obj (component_payload S D f n) x).symm h
  exact transport_edges (leftPath S f a n x) (rightPath S f a n x) aligned
    (ForwardMixed.IsTransport.app (component_payload S A f n).symm _)
    (ForwardMixed.IsTransport.map ((Iterates.layer P S (underlying Y) n).map a.op).toFunctor
      (ForwardMixed.IsTransport.app (component_payload S D f n).symm x))

/-- The native lengthwise evaluation cube commutes at every independent iterate. -/
theorem leaf_law (n : Nat) : Cube.Law (TelescopeAmbientMixed.leafMap S f a n) :=
  leaf_of_factors S f a n (TelescopePositiveBase.component_base_lift S X a n)
    (TelescopePositiveBase.component_base_lift S Y a n)

/-- The original telescope evaluation commutes with simultaneous base reindexing and an arbitrary ambient strong payload map. -/
theorem evaluation_mixed : ForwardMixed.Commuting (TelescopeAmbientMixed.evaluationCube S f a) :=
  TelescopePresentationPasting.evaluation_of_lengths S f a (leaf_law S f a)

end ContextualComposition.GrothendieckStep.TelescopeLeafCancellation
