import audit.WorkstreamAReview

namespace WorkstreamAReview.A2
open WitnessedDecompositions

def selfAssignment : S.Assignment (Tree.freeCalc S) :=
  fun g => Tree.generatorOperation (S := S) g

def changedAssignment : S.Assignment (Tree.freeCalc S)
  | .red => Tree.generatorOperation (S := S) Gen.blue
  | .root => Tree.generatorOperation (S := S) Gen.root
  | .tail => Tree.generatorOperation (S := S) Gen.tail
  | .fork => Tree.generatorOperation (S := S) Gen.fork
  | .blue => Tree.generatorOperation (S := S) Gen.blue
  | .erase => Tree.generatorOperation (S := S) Gen.erase

theorem identity_extension :
    Tree.extend (Tree.freeCalc S) selfAssignment = Calc.Hom.id (Tree.freeCalc S) := by
  symm
  apply Tree.extend_unique
  rfl

theorem parallel_primitive_assignments_distinct : selfAssignment ≠ changedAssignment := by
  intro h
  have he := congrArg (fun a : S.Assignment (Tree.freeCalc S) =>
    (a Gen.red).val.generators) h
  change [Gen.red] = [Gen.blue] at he
  cases he

theorem actual_strict_extensions_distinct :
    Tree.extend (Tree.freeCalc S) selfAssignment ≠
      Tree.extend (Tree.freeCalc S) changedAssignment := by
  intro h
  apply parallel_primitive_assignments_distinct
  have he := congrArg (Tree.restrict (Tree.freeCalc S)) h
  simpa only [Tree.restrict_extend] using he

-- An assignment cannot replace a unary primitive by an operation of the
-- same output but a different whole input profile, nor by a wrong output.
example : (Tree.freeCalc S).Operation (S.result Gen.red) (S.input Gen.red) := by
  fail_if_success exact Tree.generatorOperation (S := S) Gen.fork
  fail_if_success exact Tree.identityOperation (S := S) x
  exact selfAssignment Gen.red

#print axioms identity_extension
#print axioms parallel_primitive_assignments_distinct
#print axioms actual_strict_extensions_distinct
#print axioms Tree.restrict_extend
#print axioms Tree.extend_restrict
#print axioms Tree.homEquiv
#print axioms Tree.extend_natural_target

end WorkstreamAReview.A2
