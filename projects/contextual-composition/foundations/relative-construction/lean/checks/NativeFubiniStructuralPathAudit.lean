import ContextualComposition.NativeFubiniTreeStructuralPath

#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.medialSwap_after
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.separateSwapIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.separateSwap_trace
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.swap_cell_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.comparison_swap
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.medialRightUnit_after
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.separateRightUnitIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.separateRightUnit_trace
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.rightUnit_cell_heq
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.comparison_runit
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.FubiniTreeLaws
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.standardFubiniTreeLaws
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralMove
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralMove.joint
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralMove.separateIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralMove.fubini
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralMove.fubini_inv
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralPath
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralPath.eraseLeft
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralPath.separateIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralPath.jointIso
#print axioms ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree.StructuralPath.fubini


open ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter

open CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] {I : C}
variable (a b c d : DependentFubiniTree I)

open DependentFubiniTree

example : StructuralPath
    (.fork (.fork a .unit) (.fork b c))
    (.fork a (.fork c b)) :=
  .next (.left (.eraseRight a) (.fork b c)) (.next (.right a (.swap b c)) (.ident _))

example : StructuralPath (.fork a b) (.fork (.fork b a) .unit) :=
  .next (.swap a b) (.prev (.eraseRight (.fork b a)) (.ident _))

example : StructuralPath (.fork .unit (.fork a b)) (.fork a b) :=
  StructuralPath.eraseLeft _
