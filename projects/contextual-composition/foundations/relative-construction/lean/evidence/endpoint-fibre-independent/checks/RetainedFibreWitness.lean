import ContextualComposition.EndpointValues
import ContextualComposition.FibreParallel
import ContextualComposition.EndpointWitness
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep MovingCell ProjectedCharts EndpointValues
namespace ParallelBaseWitness
example : (restrictValue S Y A (leftTotal S Y) (leftOver S Y)).map (v 1) ≠
    (restrictValue S Y A (leftTotal S Y) (leftOver S Y)).map (v 2) := by
  rw [EndpointValues.left]; exact stageDifferent
example : (restrictValue S Y A (rightTotal S Y) (rightOver S Y)).map (v 1) ≠
    (restrictValue S Y A (rightTotal S Y) (rightOver S Y)).map (v 2) := by
  rw [EndpointValues.right]; exact oldDifferent
end ParallelBaseWitness
namespace EndpointWitness
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
example : ¬ IsIso ((restrictValue S Y d (rightTotal S Y) (rightOver S Y)).map v) := by
  rw [EndpointValues.right]
  intro h; exact noninv (isIso_of_reflects_iso v (NativePacked.compare S Y d).functor)
example : ¬ IsIso ((restrictValue S Y d (leftTotal S Y) (leftOver S Y)).map v) := by
  rw [EndpointValues.left]
  intro h; exact noninv (isIso_of_reflects_iso v (BlockEvaluation.blockwise S Y d).functor)
end EndpointWitness
