import ContextualComposition.NativeIndependentAssocNaturality

#print axioms ContextualComposition.NativeFinitePush.DependentFibre.tripleIndependentRawLeft
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.tripleIndependentRawRight
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.tripleIndependentRaw_assoc
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.collect_rectWordChart
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightTriple_collected
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleRightFlatGather
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleRightFlatGather_chart
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftTriple_collected
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleLeftFlatGather
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleLeftFlatGather_chart
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleFlatChart
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleFlatChart_natural
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleLeftFlatGather_read
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleFlatGather_assoc
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleIndependentLeftCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleIndependentRightCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleIndependentLeftCell_flat
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleIndependentRightCell_flat
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.tripleIndependentCell_assoc
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentUnitMergeLeft
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentUnitMergeRight
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentUnit_associative
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocLeftAug
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocRightAug
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocLeftAug_flat
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocRightAug_flat
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocAug_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocLeft_repr
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocRight_repr
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssocIso_pointwise_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.wordProduct_support
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.wordProductCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.wordProductMap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.wordProductMap_original_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentFamily_word
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentNativeWordMap_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentTripleLeftMap_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentTripleRightMap_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentTripleLeftCell_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentTripleRightCell_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentTripleCell_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssoc_original_native_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentAssoc_original_augmented_square


open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

private def pair : List (Fin 2) := [0, 1]
private def collapse : Fin 2 → Fin 2 := fun _ => 0
private def w := pair.product (pair.product pair)
private def g : Fin 2 × Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 :=
  Prod.map collapse (Prod.map collapse collapse)

example : wordFibre w g (0,0,0) =
    [(0,0,0),(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0),(1,1,1)] := by decide
example : wordFibre w g (0,0,1) = [] := by decide
example : (pair.product (pair.product ([] : List (Fin 2)))).isEmpty = true := by decide
