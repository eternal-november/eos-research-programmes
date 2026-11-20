module
public import ContextualComposition.AmbientExchangeFactors
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientExchangeChecklist
open CategoryTheory CategoryTheory.Functor Opposite FibreValue TelescopeSquares ContextadRoutes SpanApex NativeBlocks
open ContextadDisjointCut ContextadLawTransport ContextadModification AmbientExchangeDemand AmbientCoordinates AmbientBicategory
open AmbientDisjointFrames ContextadCellWhisker AmbientExchangeFactors
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (f g : Map S 2 1) (p : gradeCart g)
def Row (t : (power S 4).apex) {a b : Raw S X 2} (v : a ⟶ b) : Prop := Tests f g t (gradeMap v) ∧ Pure (payloadMap v)
theorem rowIff {t : (power S 4).apex} {a b : Raw S X 2} (v : a ⟶ b)
    (ha : grade (underlying X) _ a = (lhs f g).grade.obj t) (hb : grade (underlying X) _ b = (rhs f g).grade.obj t) :
    (Aligned (gradeMap v) ((disjoint f g p).grade.hom.app t) ∧ Pure (payloadMap v)) ↔ Row X f g t v :=
  and_congr_left fun _ => gradeIff f g p t (gradeMap v) ha hb
variable {a b : obj S 4 X ⟶ obj S 2 X}
theorem observed (t : a ⟶ b) (ea : encode S a = raw X (lhs f g)) (eb : encode S b = raw X (rhs f g)) :
    AmbientHorizontalRead.Reads (S := S) (X := X) (j := 4) (k := 2) t (disjoint f g p) ↔
      ∀ x, Row X f g (grade (underlying X) (power S 4).dest x) (atRaw S t x) := by
  apply (AmbientObservedCell.recognizes (S := S) (X := X) (i := 4) (j := 2) t (disjoint f g p) eb).trans
  apply forall_congr'; intro x
  exact rowIff X f g p (atRaw S t x) (congrArg (grade (underlying X) (power S 2).dest) (Functor.congr_obj ea x))
    (congrArg (grade (underlying X) (power S 2).dest) (Functor.congr_obj eb x))
set_option linter.defProp false in
def actual (m : ContextadTotal.Native S) :=
  observed (S := S) X (tensor m) (tensor m) m.cart (interchange X m).hom (disjointLeft S X m) (disjointRight S X m)
end ContextualComposition.GrothendieckStep.AmbientExchangeChecklist
