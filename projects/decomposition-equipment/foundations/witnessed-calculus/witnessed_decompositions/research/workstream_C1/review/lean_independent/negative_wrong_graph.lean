import GraphCutFragment
open WitnessedDecompositions WitnessedDecompositions.GraphCut GraphCoordinates
def impossible : CutTree (component principalGraph {0,5} 1 1 (by decide)) :=
  firstReplacement
