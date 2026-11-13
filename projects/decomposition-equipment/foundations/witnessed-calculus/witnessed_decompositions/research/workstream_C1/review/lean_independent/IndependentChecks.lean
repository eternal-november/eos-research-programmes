import GraphCutFragment

namespace C1Independent
open WitnessedDecompositions WitnessedDecompositions.GraphCut GraphCoordinates

-- Independent expected data, not aliases of the author's certificate theorem.
theorem middle_graph_is_actual_K2 :
    c1.edge.graph.val = (2, [false,true,true,false]) ∧
    c2.edge.graph.val = (2, [false,true,true,false]) := by decide

theorem exact_mixed_frontier_values :
    (Path.components (graphEvaluate leftGrouped).profile).map
      (fun c => (c.source.value.val, c.target.value.val, c.edge.graph.val.1)) =
      [(0,1,1),(1,1,2),(1,1,2),(1,2,1)] := by decide

theorem exact_refined_frontier_values :
    (Path.components (graphEvaluate refined).profile).map
      (fun c => (c.source.value.val, c.target.value.val, c.edge.graph.val.1)) =
      [(0,1,1),(1,1,1),(1,1,1),(1,1,1),(1,1,1),(1,2,1)] := by decide

theorem concrete_cross_edge_bits :
    (graphEvaluate leftGrouped).whole.val.1 = 6 ∧
    (graphEvaluate leftGrouped).whole.val.2.length = 36 ∧
    (graphEvaluate leftGrouped).whole.val.2[5]? = some false ∧
    (graphEvaluate alteredTree).whole.val.2[5]? = some true ∧
    (graphEvaluate leftGrouped).whole.val.2[30]? = some false ∧
    (graphEvaluate alteredTree).whole.val.2[30]? = some true := by decide

-- Same empty graph removes the graph-size confound in the author's negative test.
def emptyNonLoop : Component Interface := component principalGraph ∅ 0 1 (by decide)
theorem negative_control_same_empty_graph : emptyNonLoop.edge.graph = emptyColour := rfl

theorem empty_nonloop_still_has_unary_identity :
    (graphEvaluate (Tree.leaf (S := cutSignature) emptyNonLoop)).blocks = [[]] ∧
    (graphEvaluate (Tree.leaf (S := cutSignature) emptyNonLoop)).profile.length = 1 := by
  exact ⟨rfl, rfl⟩

-- All nullary signature generators retain their exact endpoint and empty graph.
theorem designated_nullary_typed (a : Interface) :
    cutSignature.source (.inr a) = a ∧ cutSignature.target (.inr a) = a ∧
    (cutSignature.output (.inr a)).graph = emptyColour ∧
    (cutSignature.input (.inr a)).length = 0 := ⟨rfl,rfl,rfl,rfl⟩

#print axioms middle_graph_is_actual_K2
#print axioms exact_mixed_frontier_values
#print axioms exact_refined_frontier_values
#print axioms concrete_cross_edge_bits
#print axioms negative_control_same_empty_graph
#print axioms empty_nonloop_still_has_unary_identity
#print axioms designated_nullary_typed
end C1Independent
