module
public import ContextualComposition.AmbientDisjointFrames
public import ContextualComposition.AmbientExchangeDemand
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientObservedCell
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadRoutes ContextadModification NativeBlocks ContextadLawTransport SpanApex
open ContextadDisjointCut AmbientDisjointFrames AmbientBicategory AmbientCoordinates AmbientExchangeDemand
open AmbientHorizontalRead ContextadCellWhisker CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 240000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X : Obj.{u,v} B} {i j : Nat} {r s : Map S i j} {a b : obj S i X ⟶ obj S j X}
theorem recognizes (t : a ⟶ b) (c : Cell r s) (eb : encode S b = raw X s) :
    Reads (S := S) (X := X) (j := i) (k := j) t c ↔ ∀ x : Raw S X i,
      Aligned (gradeMap (atRaw S t x)) (c.grade.hom.app (grade (underlying X) _ x)) ∧ Pure (payloadMap (atRaw S t x)) := by
  constructor
  · intro h x
    exact ⟨((h x).map gradeProjection).trans (NativeCube.ofEq (readGrade c X x)),
      ContextadOuterRigidity.payloadAligned (h x) (readPure c X x)⟩
  · intro h x
    exact ContextadChosenCone.alignChosen (underlying X) (power S j).dest (Functor.congr_obj eb x)
      ((h x).1.trans (NativeCube.ofEq (readGrade c X x)).symm) (h x).2 (readPure c X x)
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
def exchangeTests :=
  recognizes (S := S) (X := X) (i := 4) (j := 2) (r := lhs (tensor m) (tensor m)) (s := rhs (tensor m) (tensor m))
    (interchange X m).hom (disjoint (tensor m) (tensor m) m.cart) (disjointRight S X m)
end ContextualComposition.GrothendieckStep.AmbientObservedCell
