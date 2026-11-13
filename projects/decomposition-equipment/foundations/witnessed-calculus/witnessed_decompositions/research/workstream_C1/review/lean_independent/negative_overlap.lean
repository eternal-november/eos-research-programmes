import GraphCutFragment
open WitnessedDecompositions WitnessedDecompositions.GraphCut GraphCoordinates
def impossible := binaryCut principalGraph Finset.univ Finset.univ {0} (by decide)
  0 1 2 (by decide) (by decide)
