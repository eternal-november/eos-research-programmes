import GraphCutFragment
open WitnessedDecompositions WitnessedDecompositions.GraphCut GraphCoordinates
def impossible : CutTree (component principalGraph ∅ 0 1 (by decide)) :=
  Tree.corolla (S := cutSignature) (.inr 0)
