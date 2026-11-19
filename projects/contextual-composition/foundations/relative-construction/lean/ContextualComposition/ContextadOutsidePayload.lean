module
public import ContextualComposition.ContextadOutsideTransport
public import ContextualComposition.ContextadCellPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterRigidity
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadOuterCharts ContextadRoutes ContextadLawTransport ContextadChartDescent ContextadNativeLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (A : B)
def componentsPure {X D : Type*} [Category* X] [Category* D] {F G : X ⥤ D} (i : F ≅ G) : Prop := ∀ x, Pure (i.hom.app x)
theorem unitChartTransport : componentsPure (outerUnit (S := S) Y d A) := by
  unfold componentsPure outerUnit
  apply localWithCast
  exact outsideUnitTransport (S := S) Y d
theorem tensorChartTransport : componentsPure (outerTensor Y m A) := by
  unfold componentsPure outerTensor
  apply localWithCast
  exact outsideTensorTransport Y m
variable {Y} {Z : PackedCuts.Psh.{u,max u v,u,v} B} (t : Y ⟶ Z)
theorem chartInput {i j : Nat} (r : Map S i j) (x) :
    ((ChainPayload.layerMap t S j).app (op A)).toFunctor.obj ((evaluate Y r A).obj x) =
      (evaluate Z r A).obj (((ChainPayload.layerMap t S i).app (op A)).toFunctor.obj x) :=
  (ContextadPayloadModification.evalAligned t (ContextadCellPasting.idCell r) A x).src
theorem unitPayload (x) : Aligned (((ChainPayload.layerMap t S 2).app (op A)).toFunctor.map ((outerUnit (S := S) Y d A).hom.app x))
    ((outerUnit (S := S) Z d A).hom.app (((ChainPayload.layerMap t S 1).app (op A)).toFunctor.obj x)) :=
  alignTransports (chartInput A t (suffix (insert S d)) x) (pureMap _ (unitChartTransport Y d A x)) (unitChartTransport Z d A _)
theorem tensorPayload (x) : Aligned (((ChainPayload.layerMap t S 2).app (op A)).toFunctor.map ((outerTensor Y m A).hom.app x))
    ((outerTensor Z m A).hom.app (((ChainPayload.layerMap t S 3).app (op A)).toFunctor.obj x)) :=
  alignTransports (chartInput A t (suffix (tensor m)) x) (pureMap _ (tensorChartTransport Y m A x)) (tensorChartTransport Z m A _)
end ContextualComposition.GrothendieckStep.ContextadOuterRigidity
