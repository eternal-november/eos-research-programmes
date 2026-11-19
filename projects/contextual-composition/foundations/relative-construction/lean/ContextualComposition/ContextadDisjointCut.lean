module
public import ContextualComposition.ContextadTriangleSchedule
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadDisjointCut
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadSchedule ContextadLawTransport
open TelescopeSquares NativeAssoc FibreValue NativeTrace NativeCleavage
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
abbrev leaf (U : NativeBlocks.Span (B := B)) :
    (append P S (append P S U)).apex ⥤ (power S 2).apex :=
  SpanPayload.totalMap P.grades (second P U.dest) (right P S) rfl
theorem leafFront (U : NativeBlocks.Span (B := B)) : leaf S U ⋙ front S 1 = gradeProjection ⋙ second P U.dest := rfl
theorem leafTip (U : NativeBlocks.Span (B := B)) : leaf S U ⋙ last S 1 = second P (append P S U).dest := rfl
abbrev leaf₁ : (power S 3).apex ⥤ (power S 2).apex := leaf S (power S 1)
abbrev leaf₂ : (power S 4).apex ⥤ (power S 2).apex := leaf S (power S 2)
theorem tail₁ : (blocks S 1 2).rest = leaf₁ S := by
  apply snoc_ext S 1
  · rw [cut_rest S 1 1,ContextadOuterCharts.tailOne]; rfl
  · exact (cut_tip S 1 1).trans (leafTip S (power S 1)).symm
set_option maxHeartbeats 1700000 in
theorem tail₂ : (blocks S 2 2).rest = leaf₂ S := by
  apply snoc_ext S 1
  · rw [cut_rest S 2 1,ContextadOuterCharts.tailOne]; rfl
  · rw [cut_tip S 2 1]
    change last S 3 = leaf S (power S 2) ⋙ last S 1
    rw [leafTip]; rfl
variable {S} {U V : NativeBlocks.Span (B := B)} (r : Operation U V)
abbrev double := appendMap (S := S) (appendMap (S := S) r)
abbrev moveRaw : (double (S := S) r).grade ⋙ leaf S V ⟶ leaf S U :=
  ContextadOuterCharts.liftTail (e := second P U.dest) (e' := second P V.dest) P.grades (right P S) (appendMap (S := S) r).grade (suffixRaw (P := P) (U := U) (V := V) r.grade r.leg)
theorem cartRaw (x) : Cartesian (power S 2).source ((moveRaw (S := S) r).app x) :=
  ContextadOuterCharts.liftCart (e := second P U.dest) (e' := second P V.dest) P.grades (right P S) (appendMap (S := S) r).grade (suffixRaw (P := P) (U := U) (V := V) r.grade r.leg) (left P)
    (fun z => cartesianLift P.grades (𝟭 B) ((second P U.dest).obj z) (r.leg.app (grade _ _ z))) x
variable (f g : Map S 2 1)
noncomputable abbrev wide : Map S 4 3 := suffix (suffix f)
noncomputable abbrev lhs : Map S 4 2 := comp (wide f) (inside 1 g)
noncomputable abbrev rhs : Map S 4 2 := comp (inside 2 g) (suffix f)
noncomputable abbrev move : (wide f).grade ⋙ leaf₁ S ⟶ leaf₂ S :=
  moveRaw (S := S) (U := power S 2) (V := power S 1) f
theorem cartMove (x) : Cartesian (power S 2).source ((move f).app x) :=
  cartRaw (S := S) (U := power S 2) (V := power S 1) f x
theorem leftTail : (lhs f g).grade ⋙ last S 1 = (wide f).grade ⋙ leaf₁ S ⋙ g.grade := by
  change (wide f).grade ⋙ (inside 1 g).grade ⋙ last S 1 = _
  rw [← ContextadOuterCharts.tailOne (S := S) 1,inTail,tail₁]
theorem rightTail : (inside 2 g).grade ⋙ last S 2 = leaf₂ S ⋙ g.grade := by
  rw [← ContextadOuterCharts.tailOne (S := S) 2,inTail,tail₂]
theorem headLeft : (lhs f g).grade ⋙ front S 1 = (blocks S 2 2).first ⋙ f.grade := by
  change (wide f).grade ⋙ (inside 1 g).grade ⋙ (blocks S 1 1).first = _
  rw [inHead]
  change ((suffix (suffix f)).grade ⋙ front S 2) ⋙ front S 1 = _ 
  rw [snocHead,Functor.assoc,snocHead]
  rfl
theorem headRight : (rhs f g).grade ⋙ front S 1 = (blocks S 2 2).first ⋙ f.grade := by
  change (inside 2 g).grade ⋙ (suffix f).grade ⋙ front S 1 = _
  rw [snocHead,← Functor.assoc]
  exact congrArg (· ⋙ f.grade) (inHead 2 g)
end ContextualComposition.GrothendieckStep.ContextadDisjointCut
