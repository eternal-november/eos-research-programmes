module
public import ContextualComposition.AmbientActualIso
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFourToTwo
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport ContextadDisjointCut AmbientBicategory AmbientCoordinates
open AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientExchangeDemand AmbientFlatTerminal AmbientDisjointFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
open ContextadModification AmbientPackedTips AmbientNativeTerminal ContextadWeakWeight
variable (f g : Map S 2 1) (pg : gradeCart g)
variable {a b : obj S 4 X ⟶ obj S 2 X} (z : a ≅ b)
theorem reveal (h : Reading X f g pg z.inv) :
    AmbientHorizontalRead.Reads (S := S) (X := X) (j := 4) (k := 2) (r := lhs f g) (s := rhs f g) z.symm.hom (disjoint f g pg) := h
set_option linter.defProp false in
def visible := reveal X (tensor m) (tensor m) m.cart (squareM S m (M S X m)) (current X m)
end
end ContextualComposition.GrothendieckStep.AmbientFourToTwo
