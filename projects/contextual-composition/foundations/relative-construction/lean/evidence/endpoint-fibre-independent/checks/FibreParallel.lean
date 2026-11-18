module
public import ContextualComposition.ParallelBaseWitness
@[expose] public section
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep MovingCoordinates NativePacked
namespace ParallelBaseWitness
noncomputable abbrev A := (base S Y).obj (J.obj z)
noncomputable abbrev w : CutCompositor.W S Y A :=
  pair Y _ (grade _ _ (point S Y (J.obj z))) B.star
noncomputable def v (n : Nat) : w ⟶ w := arrow (𝟙 _) (show Nat from n)
theorem raw (n : Nat) : (payloadMap (v n) : Nat) = n := rfl
theorem fibreDifferent : v 1 ≠ v 2 := by
  intro h
  have q := congrArg (fun f : w ⟶ w => (payloadMap f : Nat)) h
  exact (by decide : (1:Nat) ≠ 2) ((raw 1).symm.trans (q.trans (raw 2)))
theorem oldDifferent : (CutCompositor.previous S Y A).map (v 1) ≠ (CutCompositor.previous S Y A).map (v 2) := by
  intro h
  exact fibreDifferent ((NativePacked.compare S Y A).functor.map_injective h)
theorem stageDifferent : (CutCompositor.stages S Y A).map (v 1) ≠ (CutCompositor.stages S Y A).map (v 2) := by
  intro h
  exact fibreDifferent ((BlockEvaluation.blockwise S Y A).functor.map_injective h)
end ParallelBaseWitness
