module
public import ContextualComposition.ContextadOuterRigidity
public import ContextualComposition.ContextadAppendCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterWhisker
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex FibreValue TelescopeSquares ContextadAppendCells
open ContextadOuterCharts ContextadRoutes ContextadOuterRigidity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {U V : Span (B := B)} {p q : Operation U V} (a : ApexCell p q)
abbrev weighted (Y : PackedCuts.Psh.{u,max u v,u,v} B) {U V : Span (B := B)} {p q : Operation U V} (a : ApexCell p q) :=
  WeightedCells.weightIso Y U.dest V.dest a.grade a.tip
noncomputable abbrev extended := weighted Y (appendCell (S := S) a)
theorem stageEq (f : Operation U V) : fstWay (S := S) Y f = sndWay (S := S) Y f :=
  Functor.ext_of_iso (stageComparison (S := S) Y f) (fun x => (stagePure (S := S) Y f x).choose) (fun x => (stagePure (S := S) Y f x).choose_spec)
theorem readPayload {K : Type*} [Category* K] (H : PackedCuts.Psh.{u,max u v,u,v} B) (e : K ⥤ B)
    {x y : Total H e} (f : x ⟶ y) (h : Pure (payloadMap ((NativeTrace.leaf H e).map f))) : Pure (payloadMap f) := h
theorem fibreOfPre {K L : Type*} [Category* K] [Category* L] (r : K ⥤ L) (d : L ⥤ B)
    {x y : Total Y (r ⋙ d)} (z : x ⟶ y) (q : Pure (payloadMap z)) :
    Pure (payloadMap ((SpanPayload.totalMap Y r d rfl).map z)) := q
theorem gradeOfLast {K : Type*} [Category* K] (e : K ⥤ B) {x y : Total Y (second P e ⋙ right P S)} (z : x ⟶ y)
    (p : Pure (payloadMap (gradeMap z))) : Pure (payloadMap (gradeMap ((SpanPayload.totalMap Y (second P e) (right P S) rfl).map z))) := p
set_option maxHeartbeats 1200000 in
theorem unpackLast (V : Span (B := B)) {x y : Total Y (append P S V).dest} (z : x ⟶ y)
    (p : Pure (payloadMap (gradeMap z))) (q : Pure (payloadMap z)) :
    Pure (payloadMap (((ContextadOuterCharts.last (S := S) Y V ⋙ BlockEvaluation.global S Y 1).map z))) := by
  rw [Functor.comp_map]
  apply decodedChosen.{u,v}
  · apply gradeOfLast; exact p
  · apply fibreOfPre; exact q
set_option maxHeartbeats 1200000 in
theorem stagePayload (V : Span (B := B)) {x y : Total Y (append P S V).dest} (z : x ⟶ y)
    (p : Pure (payloadMap (gradeMap z))) (q : Pure (payloadMap z)) : Pure (payloadMap ((stage (S := S) Y V).map z)) := by
  apply readPayload
  change Pure (payloadMap (((stage (S := S) Y V ⋙ NativeTrace.leaf (LY (S := S) Y) V.dest).map z)))
  rw [stageLeaf]
  apply unpackLast <;> assumption
theorem twoPure (x) : Pure (payloadMap ((stage (S := S) Y V).map ((extended (S := S) Y a).hom.app x))) := by
  apply stagePayload
  · rw [show gradeMap ((extended (S := S) Y a).hom.app x) = _ from WeightedCells.weightGrade Y _ _ (appendCell (S := S) a).grade (appendCell (S := S) a).tip x]
    exact WeightedCells.weightPayloadPure P.grades _ _ a.grade a.tip _
  · exact WeightedCells.weightPayloadPure Y _ _ (appendCell (S := S) a).grade (appendCell (S := S) a).tip x
theorem gradeAligned (x) :
    Aligned (gradeMap ((stage (S := S) Y V).map ((extended (S := S) Y a).hom.app x)))
      (gradeMap ((weighted (LY (S := S) Y) a).hom.app ((stage (S := S) Y U).obj x))) := by
  let z := (extended (S := S) Y a).hom.app x
  apply (NativeCube.functorAlign (stageHead (S := S) Y V) z).trans
  change Aligned (gradeMap (gradeMap z)) _
  rw [show gradeMap z = _ from WeightedCells.weightGrade Y _ _ (appendCell (S := S) a).grade (appendCell (S := S) a).tip x]
  rw [show gradeMap ((appendCell (S := S) a).grade.hom.app _) = _ from WeightedCells.weightGrade P.grades _ _ a.grade a.tip _]
  rw [show gradeMap ((weighted (LY (S := S) Y) a).hom.app _) = _ from WeightedCells.weightGrade (LY (S := S) Y) _ _ a.grade a.tip _]
  exact ContextadPayloadModification.appChange a.grade.hom (Functor.congr_obj (stageHead (S := S) Y U).symm x)
theorem whisker (x) : Aligned ((stage (S := S) Y V).map ((extended (S := S) Y a).hom.app x))
    ((weighted (LY (S := S) Y) a).hom.app ((stage (S := S) Y U).obj x)) :=
  ContextadUnitTotal.pureAlign (LY (S := S) Y) V.dest (Functor.congr_obj (stageEq (S := S) Y p) x)
    (Functor.congr_obj (stageEq (S := S) Y q) x) _ _ (gradeAligned Y a x) (twoPure Y a x)
    (WeightedCells.weightPayloadPure (LY (S := S) Y) _ _ a.grade a.tip _)
end ContextualComposition.GrothendieckStep.ContextadOuterWhisker
