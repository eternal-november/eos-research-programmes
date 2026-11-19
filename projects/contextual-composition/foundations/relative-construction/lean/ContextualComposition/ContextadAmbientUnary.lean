module
public import ContextualComposition.ContextadAmbientCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue NativeCleavage
open ContextadWeakAction ContextadModification BoundaryPaste SpanApex TelescopeSquares NativeBlocks
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z W : PackedCuts.Psh.{u,max u v,u,v} B}
variable (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor')
noncomputable def layerTotal := (BlockEvaluation.global S Y 1).strictInv ⋙ atEndpoint a (right P S) ⋙ BlockEvaluation.global S Z 1
theorem layerOver : layerTotal S a ⋙ proj (PackedFree.pow S Z 1) = proj (PackedFree.pow S Y 1) := by
  unfold layerTotal
  simp only [Functor.assoc]
  rw [show BlockEvaluation.global S Z 1 ⋙ proj (PackedFree.pow S Z 1) = _ from BlockEvaluation.globalOver S Z 1]
  rw [← Functor.assoc (atEndpoint a (right P S)),show atEndpoint a (right P S) ⋙ gradeProjection = _ from actionGrade (right P S) (totalStrong a) (strongOver a)]
  exact invOver _ _ _ (BlockEvaluation.globalOver S Y 1)
theorem layerPres : Pres (layerTotal S a) (proj (PackedFree.pow S Y 1)) (proj (PackedFree.pow S Z 1)) := by
  intro x y f h
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Z 1) (BlockCartesian.isoIncoming _) _ _).mp
  rw [BlockEvaluation.globalOver]
  apply liftCart a (right P S) (left P) (nativeChoice (S := S) 1)
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Y 1).strictInv (BlockCartesian.isoIncoming _) _ _).mp
  change Cartesian ((BlockEvaluation.global S Y 1).strictInv ⋙ gradeProjection ⋙ (power S 1).source) f
  rwa [invOver _ _ _ (BlockEvaluation.globalOver S Y 1)]
noncomputable def layerStrong : StrongTrans (PackedFree.pow S Y 1).toPseudofunctor' (PackedFree.pow S Z 1).toPseudofunctor' :=
  decodedStrong _ _ (layerTotal S a) (layerOver S a) (layerPres S a)
theorem layerComp : layerTotal S (a.vcomp b) = layerTotal S a ⋙ layerTotal S b :=
  (BlockEvaluation.cancelMiddle (BlockEvaluation.global S Y 1).strictInv (atEndpoint a (right P S))
    (BlockEvaluation.global S Z 1) (BlockEvaluation.global S Z 1).strictInv (atEndpoint b (right P S)) (BlockEvaluation.global S W 1)
    (atEndpoint (a.vcomp b) (right P S)) (BlockEvaluation.global S Z 1).asIsomorphism.unit_eq.symm (atEndpointComp a b (right P S)).symm).symm
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
