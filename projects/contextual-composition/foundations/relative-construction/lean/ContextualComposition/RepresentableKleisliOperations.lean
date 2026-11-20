module
public import ContextualComposition.RepresentableStrictEmbedding
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliOperations
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames ContextadAmbientPayload ContextadCoherence
open ContextadRoutes ContextadModification FibreValue NativeBlocks AmbientCoherentPseudomonad ContextadNativeLaws ContextadOuterCharts
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} (S : P.Split)
abbrev ps := Bᵒᵖ ⥤ Cat.{u,u}
variable {Y Z : ps (B := B)} (t : Y ⟶ Z)
theorem extract {Y Z : ps (B := B)} (f : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (t : Y ⟶ Z)
    (h : totalStrong f = ChainPayload.fibreMap t (𝟭 B)) (A : B) :
    AmbientRoundTrip.compAt f A = (t.app (op A)).toFunctor := by
  apply ContextadFinal.cancelIncl Z A _ _
  exact (AmbientRoundTrip.strongIncl f A).trans ((congrArg (incl Y A ⋙ ·) h).trans (ContextadPayloadModification.inclSquare t A))
theorem layerStrictTotal :
    totalStrong (blockStrong (S := S) (RepresentableStrictEmbedding.strong t) 1) =
    ChainPayload.fibreMap (ChainPayload.extensionMap t S) (𝟭 B) := by
  let F := BlockEvaluation.global S Y 1
  let G := BlockEvaluation.global S Z 1
  have i : atEndpoint (RepresentableStrictEmbedding.strong t) (power S 1).dest = ChainPayload.fibreMap t (power S 1).dest :=
    (ContextadUnitTotal.congrAction (power S 1).dest _ rfl (RepresentableStrictEmbedding.encode t)).trans (ContextadWeakAction.onStrict _ t)
  have k : ChainPayload.fibreMap t (power S 1).dest ⋙ G = F ⋙ ChainPayload.fibreMap (ChainPayload.extensionMap t S) (𝟭 B) :=
    EvalPayload.nativeSquare t S 0
  refine (AmbientBlockIteration.encodedBlock S (RepresentableStrictEmbedding.strong t) 1).trans ?_
  change F.strictInv ⋙ atEndpoint (RepresentableStrictEmbedding.strong t) (power S 1).dest ⋙ G = _
  rw [i,k,← Functor.assoc]
  exact (congrArg (· ⋙ ChainPayload.fibreMap (ChainPayload.extensionMap t S) (𝟭 B)) F.asIsomorphism.counit_eq).trans (Functor.id_comp _)
theorem layerStrict (A : B) :
    AmbientRoundTrip.compAt (blockStrong (S := S) (RepresentableStrictEmbedding.strong t) 1) A = ChainPayload.fibreMap t (P.extend A) :=
  extract _ (ChainPayload.extensionMap t S) (layerStrictTotal S t) A
variable {S} (T : Data S)
theorem unitAt (Y : Obj.{u,u} B) (A : B) :
    AmbientRoundTrip.compAt (E S Y T.unit).hom A = ContextadUnit.atBase T.unit (underlying Y) A :=
  extract _ (ContextadUnit.onPresheaf T.unit S (underlying Y))
    ((AmbientHorizontalFrames.totalOper S Y (insert S T.unit) (unitCart T.unit)).trans
    (ContextadUnitTotal.totalUnit (underlying Y) T.unit)) A
theorem mulAt (Y : Obj.{u,u} B) (A : B) :
    AmbientRoundTrip.compAt (M S Y T.mult).hom A = ContextadTensor.binary (ContextadSpecialize.data T.mult) (underlying Y) A :=
  congrArg (fun F => AmbientRoundTrip.compAt F A) (AmbientOperationBoundaries.nativeMultiplication T.mult (underlying Y))
end ContextualComposition.GrothendieckStep.RepresentableKleisliOperations
