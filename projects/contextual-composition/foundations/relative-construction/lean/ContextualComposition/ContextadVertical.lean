module
public import ContextualComposition.ContextadChart
public import ContextualComposition.ContextadTotal
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadVertical
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanApex NativeBlocks ContextadChart SpanPayload.Power
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
theorem strictWeight {B K L : Type*} [Category* B] [Category* K] [Category* L]
    (Y : Bᵒᵖ ⥤ Cat.{v,u}) (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B} (h : r ⋙ d = e) :
    SpanPayload.totalMap Y r d h = restrict Y e d r (eqToHom h) := by
  subst e
  have c : restrictionCell Y (r ⋙ d) d r (eqToHom rfl) = 𝟙 (diagram Y (r ⋙ d)) := by
    apply NatTrans.ext; funext x
    exact (Y ⋙ Cat.opFunctor).map_id _
  unfold restrict
  rw [c, Grothendieck.map_id_eq]
  rfl
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (d : ContextadTensor.Data S) (A : B)
abbrev inclusion := Functor.Fiber.fiberInclusion (p := (power S 2).source) (S := A)
abbrev localGrade := gradeFunctor S 1 A ⋙ d.tensor A ⋙ one (P := P) A
abbrev localLeg := pasteLift (nativeEndpoint S 1 A) (chainsEndpoint S 1 A) (right P S)
    (gradeFunctor S 1 A) (d.tensor A ⋙ one (P := P) A) (eqToHom (gradeEndpoint S 1 A))
    (pasteLift (chainsEndpoint S 1 A) (P.extend A) (right P S) (d.tensor A) (one (P := P) A)
      (d.delta A) (eqToHom (oneEnd S A)))
/-- Recognition of the independently given vertical chart, without a payload presheaf or
any base-change arrow. The grade equality is on functors, not just objects. -/
structure Agrees : Prop where
  grade : inclusion (S := S) A ⋙ m.grade = localGrade d A
  endpoint : HEq (whiskerLeft (inclusion (S := S) A) m.delta) (localLeg d A)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev insertOne := SpanPayload.totalMap Y (one (P := P) A) (right P S) (oneEnd S A)
theorem weightedVertical (h : Agrees m d A) :
    fibreInclude A Y (power S 2).source (power S 2).dest ⋙ ContextadTotal.action m Y =
      weighted S 1 A Y ⋙ restrict Y _ _ (d.tensor A) (d.delta A) ⋙ insertOne (S := S) A Y := by
  unfold fibreInclude weighted insertOne ContextadTotal.action ContextadCartesian.weighted
  rw [strictWeight, strictWeight, strictWeight, ← restrict_paste, ← restrict_paste, ← restrict_paste]
  apply restrict_congr _ _ _ h.grade
  have q : pasteLift (nativeEndpoint S 1 A) (power S 2).dest (right P S) (inclusion (S := S) A)
      m.grade (eqToHom rfl) m.delta = whiskerLeft (inclusion (S := S) A) m.delta := Category.comp_id _
  exact (heq_of_eq q).trans h.endpoint
end ContextualComposition.GrothendieckStep.ContextadVertical
