import ContextualComposition.NativePacked
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativePacked
namespace Profile210
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
abbrev W := Lift.value Y A (pairSpan S)
def tags (x : W S Y A) : Nat × Nat :=
  let p := (grade _ _ x).val
  (p.fst.1,p.snd.1)
theorem tagOf {x y : tel S} (h : x ⟶ y) : x.1 = y.1 := by cases h; rfl
theorem invariant {x y : W S Y A} (f : x ⟶ y) : tags S Y A x = tags S Y A y :=
  Prod.ext (tagOf S (gradeMap f).val.hom.fst) (tagOf S (gradeMap f).val.hom.snd)
theorem onCut (i : Nat × Nat) (z : coords S Y A i) :
    tags S Y A ((nativeEquiv S Y A).functor.obj ⟨i,z⟩) = i := by
  let F := Lift.comp (cut S i) (tagged S i)
  have eo := Functor.congr_obj (native_at S Y A i) z
  change (nativeEquiv S Y A).functor.obj ⟨i,z⟩ = (Lift.weighted F Y A).obj z at eo
  rw [eo]
  have e1 := Functor.congr_obj (SpanPayload.total_projection Y (Lift.grade F A) _ (Lift.endpoint F A)) z
  have e2 := Functor.congr_obj (SpanPayload.fibre_diagram F.functor (pairSpan S).source F.source A) (grade _ _ z)
  let key (w : (pairSpan S).apex) := (w.fst.1,w.snd.1)
  exact (congrArg (fun t => key t.val) e1).trans (congrArg key e2)
theorem profileComparison (x : W S Y A) :
    PackedCuts.profile S Y A ((NativePacked.compare S Y A).functor.obj x) = tags S Y A x := by
  let N := nativeEquiv S Y A
  let z := N.inverse.obj x
  have lhs : PackedCuts.profile S Y A ((NativePacked.compare S Y A).functor.obj x) = z.1 :=
    PackedCuts.profile_at S Y A z.1 ((leaf S Y A z.1).functor.obj z.2)
  have rhs := onCut S Y A z.1 z.2
  exact lhs.trans (rhs.symm.trans (invariant S Y A (N.counitIso.hom.app x)))
end Profile210
