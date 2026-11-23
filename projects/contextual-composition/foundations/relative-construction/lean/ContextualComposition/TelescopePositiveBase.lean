module
public import ContextualComposition.TelescopeValueLift

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopePositiveBase
open CategoryTheory CategoryTheory.Functor Opposite
open NativeCleavage NativeBlocks CoproductSpan CoproductSpan.All SpanApex
open TelescopeSquares FibreValue AmbientBicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) (X : Obj.{u,v} B) {A D : B} (a : A ⟶ D)

set_option maxHeartbeats 300000 in
theorem base_component (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :
    (FibreValue.evalSquare S (underlying X) n a).hom.app x =
      (value (Evaluation.G S (underlying X) n) A).map ((Evaluation.fibreSquare S (underlying X) n a).hom.app x) ≫
      (valueSquare (Evaluation.G S (underlying X) n) a).hom.app ((Evaluation.onFibre S (underlying X) n D).obj x) :=
by
  have fact := TelescopeValueLift.positive_paste_data S X a n x
  dsimp only [FibreValue.evalSquare, FibreValue.eval, FibreValue.proj, Evaluation.iterateChoice,
    FibreValue.choice, Functor.comp_obj, Functor.comp_map] at fact ⊢
  exact fact

set_option maxHeartbeats 400000 in
theorem raw_factor (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :
    let H := Evaluation.G S (underlying X) n
    let J := Evaluation.onFibre S (underlying X) n D
    let t := (FibreTotal.into (underlying X) (positivePowers P S n).dest (positivePowers P S n).source D).obj x
    Aligned ((incl H A).map ((value H A).map ((Evaluation.fibreSquare S (underlying X) n a).hom.app x) ≫
        (valueSquare H a).hom.app (J.obj x)) ≫ FibreValue.arrow H a ((value H D).obj (J.obj x)))
      ((Evaluation.nativeFunctor S (underlying X) n).map
        ((Route.ofChoice (payloadChoice (underlying X) S n) a).lift t)) := by
  have h := TelescopeValueLift.positive_raw_lift S X a n x
  dsimp only [Evaluation.fibreSquare,Evaluation.onFibre,NativeCube.evaluation,Functor.comp_obj,
    Functor.isoWhiskerLeft_hom, whiskerLeft_app] at h ⊢
  exact h

set_option maxHeartbeats 400000 in
theorem native_factor (n : Nat) (x : Total (underlying X) (SpanPayload.Power.nativeEndpoint S n D)) :
    let H := Evaluation.G S (underlying X) n
    let J := Evaluation.onFibre S (underlying X) n D
    let t := (FibreTotal.into (underlying X) (positivePowers P S n).dest (positivePowers P S n).source D).obj x
    Aligned ((incl H A).map ((FibreValue.evalSquare S (underlying X) n a).hom.app x) ≫
        FibreValue.arrow H a ((value H D).obj (J.obj x)))
      ((Evaluation.nativeFunctor S (underlying X) n).map
        ((Route.ofChoice (payloadChoice (underlying X) S n) a).lift t)) := by
  have fact := raw_factor S X a n x
  dsimp only at fact ⊢
  rw [← base_component S X a n x] at fact
  exact fact

set_option maxHeartbeats 500000 in
theorem component_base_lift : (n : Nat) → (x : Total (underlying X) (leg (src S) (dst S) D n)) →
    Aligned ((incl (PackedFree.pow S (underlying X) n) A).map ((SumChange.componentBase S (underlying X) a n).hom.app x) ≫
      FibreValue.arrow (PackedFree.pow S (underlying X) n) a ((component S (underlying X) D n).functor.obj x))
      ((BlockEvaluation.global S (underlying X) n).map (TelescopeAmbientLeaf.chosen S X a n x))
  | 0, x => TelescopeAmbientLeaf.zero_base_lift S X a x
  | n+1, x => by
    have h := native_factor S X a n x
    dsimp only [SumChange.componentBase, CoproductSpan.All.component, BlockEvaluation.global, TelescopeAmbientLeaf.chosen,
      CoproductSpan.All.span, CoproductSpan.All.src, CoproductSpan.All.dst, SpanPull.All.parts,
      PackedFree.pow, Evaluation.G, FibreValue.eval, Route.ofChoice, FibreValue.proj, Evaluation.iterateChoice, FibreValue.choice, Functor.comp_obj, Functor.comp_map] at h ⊢
    exact h

end ContextualComposition.GrothendieckStep.TelescopePositiveBase
