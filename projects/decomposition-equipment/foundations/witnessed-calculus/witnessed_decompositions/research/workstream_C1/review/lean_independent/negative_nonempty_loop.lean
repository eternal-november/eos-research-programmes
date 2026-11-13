import GraphCutFragment
open WitnessedDecompositions WitnessedDecompositions.GraphCut GraphCoordinates
def impossible : CutTree c1 := Tree.corolla (S := cutSignature) (.inr 1)
