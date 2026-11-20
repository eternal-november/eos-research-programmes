module
public import ContextualComposition.AmbientRoundTrip
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientBlockIteration
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue
open ContextadModification ContextadAmbientPayload ContextadWeakAction AmbientRoundTrip WordTrace NativeBlocks
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z W : PackedCuts.Psh.{u,max u v,u,v} B}
variable (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor')
theorem encodedBlock (n : Nat) : totalStrong (blockStrong (S := S) a n) = blockTotal S a n := encodeDecode _ _ _ (blockOver S a n) (blockPres S a n)
theorem blockTrace (n : Nat) (z : E (PackedFree.pow S Y n)) :
    WordTrace.read S Z n (Edge.map (blockTotal S a n) z) =
    ((WordTrace.read S Y n z).1,Edge.map (totalStrong a) (WordTrace.read S Y n z).2) := by
  let G := BlockEvaluation.global S Y n
  let w := Edge.map G.strictInv z
  have hw : Edge.map G w = z := congrArg (fun F => Edge.map F z) G.asIsomorphism.counit_eq
  let U := atEndpoint a (power S n).dest
  have h := NativeTrace.read_global S Y n w
  rw [hw] at h
  change WordTrace.read S Z n (Edge.map (BlockEvaluation.global S Z n) (Edge.map U w)) = _
  rw [NativeTrace.read_global,h]
  apply Prod.ext
  · exact congrArg (fun F => NativeTrace.word S n (Edge.map F w)) (actionGrade (power S n).dest (totalStrong a) (strongOver a))
  · exact congrArg (fun F => Edge.map F w) (actionLeaf (power S n).dest (totalStrong a) (strongOver a))
theorem blockId (Y : PackedCuts.Psh.{u,max u v,u,v} B) (n : Nat) :
    blockStrong (S := S) (𝟙 Y.toPseudofunctor') n = 𝟙 (PackedFree.pow S Y n).toPseudofunctor' := by
  apply encodeInjective
  rw [encodedBlock,strongId]
  apply Edge.functor_ext; intro z; apply read_injective S _ n
  rw [blockTrace,strongId]; rfl
theorem blockComp (n : Nat) : blockStrong (S := S) (a.vcomp b) n =
    (blockStrong (S := S) a n).vcomp (blockStrong (S := S) b n) := by
  apply encodeInjective
  rw [encodedBlock,strongComp,encodedBlock,encodedBlock]
  apply Edge.functor_ext; intro z; apply read_injective S _ n
  change _ = WordTrace.read S W n (Edge.map (blockTotal S b n) (Edge.map (blockTotal S a n) z))
  rw [blockTrace,blockTrace,blockTrace,strongComp]; rfl
theorem blockZero : blockStrong (S := S) a 0 = a := by
  apply encodeInjective; rw [encodedBlock]
  apply Edge.functor_ext; intro z
  exact congrArg Prod.snd (blockTrace S a 0 z)
theorem oneTrace (z : E (PackedFree.pow S Y 1)) :
    one S Z (Edge.map (blockTotal S a 1) z) =
      ((one S Y z).1,Edge.map (totalStrong a) (one S Y z).2) := by
  have h := blockTrace S a 1 z
  have k := congrArg Prod.snd h
  exact Prod.ext (List.cons.inj (congrArg Prod.fst h)).1 k
theorem blockSucc (n : Nat) : layerStrong S (blockStrong (S := S) a n) = blockStrong (S := S) a (n+1) := by
  apply encodeInjective
  rw [show totalStrong (layerStrong S (blockStrong (S := S) a n)) = _ from encodedBlock S (blockStrong (S := S) a n) 1,encodedBlock]
  apply Edge.functor_ext; intro z; apply read_injective S _ (n+1)
  rw [blockTrace]
  let w := one S (PackedFree.pow S Y n) z
  change (let t := one S (PackedFree.pow S Z n) (Edge.map (blockTotal S (blockStrong (S := S) a n) 1) z)
          let r := WordTrace.read S Z n t.2
          (t.1 :: r.1,r.2)) = _
  rw [oneTrace,encodedBlock]
  dsimp only [Prod.fst,Prod.snd]
  rw [blockTrace]; rfl
theorem blockTwo : layerStrong S (layerStrong S a) = blockStrong (S := S) a 2 := blockSucc S a 1
noncomputable def layerCompositor : ModIso ((layerStrong S a).vcomp (layerStrong S b)) (layerStrong S (a.vcomp b)) :=
  eqToIso (blockComp S a b 1).symm
noncomputable def layerUnitor (Y : PackedCuts.Psh.{u,max u v,u,v} B) : ModIso (layerStrong S (𝟙 Y.toPseudofunctor')) (𝟙 (PackedFree.pow S Y 1).toPseudofunctor') :=
  eqToIso (blockId S Y 1)
end ContextualComposition.GrothendieckStep.AmbientBlockIteration
