import ContextualComposition.NativeIndependentSymmetry

#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.swapRectCell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwapCellComparison
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.addressed_mapSum_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwap_selected_cell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwap_original_native_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwap_original_augmented_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.independentSwap_involutive
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.standardIndependentSwap_involutive


open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

private def source : List Nat := [0,1]
private def target : List Nat := [0,1]
private def merge (_ : Nat) : Nat := 0

example : wordFibre source merge 0 = [0,1] := by decide
example : wordFibre source merge 1 = [] := by decide
example : wordFibre (source.product source) (Prod.map merge merge) (0,0) =
    [(0,0),(0,1),(1,0),(1,1)] := by decide
