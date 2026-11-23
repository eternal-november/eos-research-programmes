module
public import ContextualComposition.TelescopeGradeChange
public import ContextualComposition.AmbientInsideMate

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientComponents
open CategoryTheory CategoryTheory.Functor Opposite CategoryTheory.Pseudofunctor
open NativeCleavage SpanApex NativeBlocks ContextadAmbientPayload CoproductSpan CoproductSpan.All
open AmbientBicategory AmbientCoordinates
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) (A : B)

/-- Evaluation followed by the fibre inclusion agrees on whole functors with the independent global chart. -/
theorem component_incl (Y : PackedCuts.Psh.{u,max u v,u,v} B) (n : Nat) :
    (component S Y A n).functor ⋙ FibreValue.incl (PackedFree.pow S Y n) A =
      SpanPayload.Power.fibreInclude A Y (power S n).source (power S n).dest ⋙ BlockEvaluation.global S Y n := by
  rw [← BlockEvaluation.global_agrees S Y A n]
  let G := BlockEvaluation.global S Y n
  let H := PackedFree.pow S Y n
  let E := FibreTotal.into Y (power S n).dest (power S n).source A
  let J := SpanPayload.fibreFunctor G (FibreValue.proj H) (BlockEvaluation.globalOver S Y n) A
  let I := Functor.Fiber.fiberInclusion (p := FibreValue.proj H) (S := A)
  exact (congrArg (fun U => E ⋙ J ⋙ U ⋙ I) (FibreValue.value_embed H A)).trans
    (congrArg (E ⋙ ·) (SpanPayload.fibre_diagram G _ (BlockEvaluation.globalOver S Y n) A))

variable {X Y : Obj.{u,v} B} (f : X ⟶ Y)
noncomputable abbrev target (n : Nat) :=
  AmbientRoundTrip.compAt (AmbientBicategory.map S n f).hom A

private theorem paste {A B C D E F G H : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F] [Category* G] [Category* H]
    (cx : A ⥤ B) (cy : C ⥤ D) (l : A ⥤ C) (q : B ⥤ D) (ix : B ⥤ E) (iy : D ⥤ F)
    (sx : A ⥤ G) (sy : C ⥤ H) (gx : G ⥤ E) (gy : H ⥤ F) (m : E ⥤ F) (v : G ⥤ H)
    (a₁ : q ⋙ iy = ix ⋙ m) (a₂ : cx ⋙ ix = sx ⋙ gx) (a₃ : gx ⋙ m = v ⋙ gy)
    (a₄ : sx ⋙ v = l ⋙ sy) (a₅ : sy ⋙ gy = cy ⋙ iy) :
    (cx ⋙ q) ⋙ iy = (l ⋙ cy) ⋙ iy :=
  (congrArg (cx ⋙ ·) a₁).trans ((congrArg (· ⋙ m) a₂).trans
    ((congrArg (sx ⋙ ·) a₃).trans ((congrArg (· ⋙ gy) a₄).trans (congrArg (l ⋙ ·) a₅))))

set_option maxHeartbeats 400000 in
theorem component_in_total (n : Nat) :
    ((component S (underlying X) A n).functor ⋙ target (X := X) (Y := Y) S A f n) ⋙
      FibreValue.incl (PackedFree.pow S (underlying Y) n) A =
      (atEndpoint f.hom (leg (src S) (dst S) A n) ⋙ (component S (underlying Y) A n).functor) ⋙
        FibreValue.incl (PackedFree.pow S (underlying Y) n) A := by
  let ix := FibreValue.incl (PackedFree.pow S (underlying X) n) A
  let iy := FibreValue.incl (PackedFree.pow S (underlying Y) n) A
  let sx := SpanPayload.Power.fibreInclude A (underlying X) (power S n).source (power S n).dest
  let sy := SpanPayload.Power.fibreInclude A (underlying Y) (power S n).source (power S n).dest
  let a := f.hom
  let m := (AmbientBicategory.map S n f).hom
  let l := atEndpoint a (leg (src S) (dst S) A n)
  let v := atEndpoint a (power S n).dest
  exact paste (component S (underlying X) A n).functor (component S (underlying Y) A n).functor
    l (AmbientRoundTrip.compAt m A) ix iy sx sy (chart S X n) (chart S Y n) (totalStrong m) v
    (AmbientRoundTrip.strongIncl m A) (component_incl S A (underlying X) n)
    (AmbientInsideMate.chartAction (S := S) (X := X) (Y := Y) f n).symm
    (TelescopeGradeChange.totalMap_payload (Y := underlying X) (Z := underlying Y) a
      (Functor.Fiber.fiberInclusion (p := (power S n).source) (S := A)) (power S n).dest rfl)
    (component_incl S A (underlying Y) n).symm

private theorem cancel_injective {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : D ⥤ E) [J.Faithful] (inj : Function.Injective J.obj)
    {F G : C ⥤ D} (h : F ⋙ J = G ⋙ J) : F = G := by
  refine Functor.ext (fun x => inj (Functor.congr_obj h x)) ?_
  intro x y g
  apply J.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using Functor.congr_hom h g

private theorem incl_injective (Z : PackedCuts.Psh.{u,max u v,u,v} B) :
    Function.Injective (FibreValue.incl Z A).obj := by
  intro x y h
  exact (Sigma.mk.inj_iff.mp (congrArg (BlockEvaluation.totalPoints Z (𝟭 B)) h)).2.eq

/-- The actual strong map on each independent iterate agrees with weighted strong payload change
under the entire lengthwise evaluation functor. -/
theorem component_payload (n : Nat) :
    (component S (underlying X) A n).functor ⋙ target (X := X) (Y := Y) S A f n =
      atEndpoint f.hom (leg (src S) (dst S) A n) ⋙ (component S (underlying Y) A n).functor := by
  let H := PackedFree.pow S (underlying Y) n
  let _ : (FibreValue.incl H A).Faithful :=
    (inferInstance : (FibreValue.embed H A ⋙ Functor.Fiber.fiberInclusion).Faithful)
  exact cancel_injective (FibreValue.incl H A) (incl_injective A H) (component_in_total S A f n)

/-- The original telescope evaluation has its comparison square on every ambient strong payload map. -/
noncomputable def evaluation_payload :
    (evaluation S (underlying X) A).functor ⋙ ZeroPower.Sum.map (target (X := X) (Y := Y) S A f) ≅
      atEndpoint f.hom (wholeLeg (src S) (dst S) A) ⋙ (evaluation S (underlying Y) A).functor :=
  TelescopeGradeChange.evaluation_of_components f.hom S A (target (X := X) (Y := Y) S A f)
    (fun n => eqToIso (component_payload S A f n))

end ContextualComposition.GrothendieckStep.TelescopeAmbientComponents
