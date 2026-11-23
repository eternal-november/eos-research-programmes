import ContextualComposition.NativeDependentLeftUnitNaturality

#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnit_whole_cell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnit_whole_cell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput_terms
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput_inner
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput_cell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput_native_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.dependentRightUnitIso_pointwise_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnit_original_native_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftInput_innerNative
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.singleton_indexedAugmentation_eq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnitLiftAugMap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.rightUnit_original_augmented_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftInput
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftInput_read
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftInput_outerNative
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftInput_cell
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftInput_native_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.dependentLeftUnitIso_pointwise_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnit_original_native_square
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnitLiftAugMap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.leftUnit_original_augmented_square


open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

private def pair : List (Fin 2) := [0, 1]
private def collapse : Fin 2 → Fin 2 := fun _ => 0
private def rightWord := dependentWord pair (fun _ => [PUnit.unit])
private def leftWord := dependentWord [PUnit.unit] (fun _ => pair)
private def rightMap : Fin 2 × PUnit → Fin 2 × PUnit := Prod.map collapse id
private def leftMap : PUnit × Fin 2 → PUnit × Fin 2 := Prod.map id collapse

example : wordFibre rightWord rightMap (0,PUnit.unit) = [(0,PUnit.unit),(1,PUnit.unit)] := by decide
example : wordFibre rightWord rightMap (1,PUnit.unit) = [] := by decide
example : wordFibre leftWord leftMap (PUnit.unit,0) = [(PUnit.unit,0),(PUnit.unit,1)] := by decide
example : wordFibre leftWord leftMap (PUnit.unit,1) = [] := by decide
