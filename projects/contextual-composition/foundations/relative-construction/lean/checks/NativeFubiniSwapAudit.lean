import ContextualComposition.NativeFubiniSwap

#print axioms ContextualComposition.NativeFinitePush.DependentFibre.colGather_swap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.independentCell_swap_transposed
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGrid
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGridOut
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGridOut_retag
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGridOut_eval
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGridOut_act
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRawLeftCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRawRightCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRawCell_preserves
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRawLeftCell_read
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapGridOut_word
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRawRightCell_read
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwapReadComparison
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.WordAugReadComparison.toIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.WordAugReadComparison.toIso_trace
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.MedialSwap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.standardMedialSwap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwapIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwapIso_trace
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.standardSwapUnit
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData.jointSwapComparison
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData.jointSwap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData.separateSwap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData.actual_fubini_swap


open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

private def xs : List Nat := [0,1]
private def ys : List Nat := [2,3]

example : (swapGridOut xs ys).leaves = [(0,2),(1,2),(0,3),(1,3)] := by decide
example : (swapGridOut xs ys).leaves ≠ xs.product ys := by decide
example : (swapGridOut xs ([] : List Nat)).leaves = [] := by decide
example : (swapGridOut ([] : List Nat) ys).leaves = [] := by decide
