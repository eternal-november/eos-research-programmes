import E3GraphGroupoidCore
import E1FiniteExamples

/-! A checked finite groupoid/graph core instance, linked to original C1 N=6
and original E1 arbitrary-function relational cells. No full-equipment Lean claim. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace E3FiniteExamples
open WitnessedDecompositions E3GraphGroupoidCore
open GraphCoordinates

def τ : Grade := Equiv.swap 0 1
def σ : Grade := Equiv.swap 1 2

theorem nonidentity_automorphism : τ ≠ (1 : Vertical (0 : Interface) 0) := by decide
theorem noncommuting_changes : σ * τ ≠ τ * σ := by decide

def component (G : Graph) (s : Block) (a b : Interface) (h : Grade) : Component Interface :=
  ⟨a,b,⟨GraphCut.colour G s,h⟩⟩
def c0 := component GraphCut.principalGraph GraphCut.B0 0 1 τ
def c1 := component GraphCut.principalGraph GraphCut.B1 1 1 1
def c2 := component GraphCut.principalGraph GraphCut.B2 1 1 1
def c3 := component GraphCut.principalGraph GraphCut.B3 1 2 σ
def whole := component GraphCut.principalGraph Finset.univ 0 2 (σ*τ)

def split01 := ofC1 GraphCut.split01 τ 1
def split23 := ofC1 GraphCut.split23 1 σ
def split0123 := ofC1 GraphCut.split0123 τ σ
def split123 := ofC1 GraphCut.split123 1 σ
def split0_123 := ofC1 GraphCut.split0_123 τ σ

def cut {g : Binary}
    (x : CutTree ⟨g.a,g.b,⟨g.left,g.first⟩⟩)
    (y : CutTree ⟨g.b,g.c,⟨g.right,g.second⟩⟩) :
    CutTree ⟨g.a,g.c,⟨g.whole,g.second*g.first⟩⟩ :=
  WitnessedDecompositions.Tree.node (S := signature) (.inl g) (Examples.binaryChildren x y)

def leftGrouped : CutTree whole :=
  cut (g := split0123)
    (cut (g := split01) (.leaf c0) (.leaf c1))
    (cut (g := split23) (.leaf c2) (.leaf c3))
def rightGrouped : CutTree whole :=
  cut (g := split0_123) (.leaf c0)
    (cut (g := split123) (.leaf c1)
      (cut (g := split23) (.leaf c2) (.leaf c3)))

def flatProfile : Quiver.Path (V := Interface) 0 2 :=
  (((Quiver.Path.nil.cons c0.edge).cons c1.edge).cons c2.edge).cons c3.edge

theorem mixed_frontier : Tree.frontier leftGrouped = flatProfile ∧
    Tree.frontier rightGrouped = flatProfile := ⟨rfl,rfl⟩

theorem repeated_nonempty : GraphCut.B1.Nonempty ∧ GraphCut.B2.Nonempty ∧ c1 = c2 := by
  refine ⟨by decide,by decide,?_⟩
  unfold c1 c2 component
  congr 2

theorem principal_blocks : (evaluate leftGrouped).blocks = [[0],[1,3],[2,4],[5]] := by decide

theorem competing_groupings_same_full_cut : evaluate leftGrouped = evaluate rightGrouped := by rfl

def splitFirst := ofC1 GraphCut.splitFirst 1 1
def splitSecond := ofC1 GraphCut.splitSecond 1 1

def firstReplacement : CutTree c1 := Tree.corolla (S := signature) (.inl splitFirst)
def secondReplacement : CutTree c2 := Tree.corolla (S := signature) (.inl splitSecond)

theorem distinct_refinements :
    (evaluate firstReplacement).whole = (evaluate secondReplacement).whole ∧
    (evaluate firstReplacement).profile = (evaluate secondReplacement).profile ∧
    (evaluate firstReplacement).blocks = [[0],[1]] ∧
    (evaluate secondReplacement).blocks = [[1],[0]] ∧
    evaluate firstReplacement ≠ evaluate secondReplacement := by
  refine ⟨rfl,rfl,by decide,by decide,?_⟩
  intro h
  have hh := congrArg FullCut.blocks h
  have hn : (evaluate firstReplacement).blocks ≠ (evaluate secondReplacement).blocks := by decide
  exact hn hh

def cutForest {g : Binary}
    (x : CutTree ⟨g.a,g.b,⟨g.left,g.first⟩⟩)
    (y : CutTree ⟨g.b,g.c,⟨g.right,g.second⟩⟩)
    (fx : Tree.Substitution x) (fy : Tree.Substitution y) :
    Tree.Substitution (cut (g := g) x y)
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => fx
  | .inr () => fy

def differentForest : Tree.Substitution rightGrouped :=
  cutForest (g := split0_123) (.leaf c0)
    (cut (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3)))
    (.leaf c0)
    (cutForest (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3))
      firstReplacement
      (cutForest (g := split23) (.leaf c2) (.leaf c3) secondReplacement (.leaf c3)))

def refined : CutTree whole := Tree.graft rightGrouped differentForest

theorem proper_occurrencewise_refinement :
    (evaluate refined).whole = GraphCut.colour GraphCut.principalGraph Finset.univ ∧
    (evaluate refined).blocks = [[0],[1],[3],[4],[2],[5]] ∧
    (evaluate refined).profile.length = 6 := ⟨rfl,by decide,rfl⟩

/-- A concrete tree evaluation is certified as a complete semantic Cell, with
its real ordered profile/partition and scalar, not just shape/endpoint checks. -/
def principalCell (n : ZMod 2) : Cell flatProfile whole.edge 1 1 where
  cut := ⟨[[0],[1,3],[2,4],[5]], by
    refine ⟨GraphCut.principalGraph,Finset.univ,[GraphCut.B0,GraphCut.B1,GraphCut.B2,GraphCut.B3],
      GraphCut.principal_partition_valid,rfl,?_,?_⟩
    · rfl
    · decide⟩
  weight := n
  square := by simp [flatProfile,pathGrade,c0,c1,c2,c3,whole,component]

theorem actual_core_semantic_bridge :
    (evaluate leftGrouped).profile = flatProfile ∧
    (evaluate leftGrouped).whole = whole.edge.graph ∧
    (evaluate leftGrouped).blocks = (principalCell 0).cut.blocks ∧
    (evaluate leftGrouped).weight = (principalCell 0).weight := ⟨rfl,rfl,by decide,rfl⟩

theorem parallel_semantic_witnesses : principalCell 0 ≠ principalCell 1 := by
  intro h
  have hh := congrArg Cell.weight h
  have hn : (0 : ZMod 2) ≠ 1 := by decide
  exact hn hh

def boundaryTarget : (2 : Interface) ⟶ 0 :=
  ⟨whole.edge.graph,σ * pathGrade flatProfile * τ⁻¹⟩
def boundaryCell : Cell flatProfile boundaryTarget τ σ :=
  ⟨(principalCell 1).cut,1,by simp [boundaryTarget,mul_assoc]⟩
def boundaryLift : Cell flatProfile (E3GraphGroupoidCore.restrict (a := (0 : Interface))
    (b := (2 : Interface)) boundaryTarget τ σ) 1 1 :=
  restrictionEquiv flatProfile boundaryTarget τ σ 1 1 (by simpa using boundaryCell)

theorem nonglobular_factorization :
    restrictionCompose flatProfile boundaryTarget τ σ 1 1 boundaryLift =
      (show Cell flatProfile boundaryTarget (τ*1) (σ*1) from by simpa using boundaryCell) :=
  restriction_factorization flatProfile boundaryTarget τ σ 1 1 _

theorem nonglobular_full_payload : boundaryLift.cut.blocks = [[0],[1,3],[2,4],[5]] ∧
    boundaryLift.weight = 1 := ⟨rfl,rfl⟩

def scalar0 : CutTree c1 := Tree.corolla (S := signature) (.inl splitFirst)
def scalar1 : CutTree c1 := Tree.corolla (S := signature) (.inl {splitFirst with weight := 1})

theorem scalar_pair_distinct : scalar0 ≠ scalar1 := by
  intro h
  have hh := congrArg (fun t : CutTree c1 => (evaluate t).weight) h
  have hn : (0 : ZMod 2) ≠ 1 := by decide
  exact hn hh

theorem scalar_erasure_nonfaithful : eraseScalar.map scalar0 = eraseScalar.map scalar1 := by
  change Tree.interpret coreCalc eraseAssignment (Tree.corolla _) =
    Tree.interpret coreCalc eraseAssignment (Tree.corolla _)
  rw [Tree.interpret_corolla]

theorem scalar_erasure_retains_partition :
    (evaluate (eraseScalar.map scalar1)).blocks = (evaluate scalar1).blocks := by decide

/-- Original C1's retained cross-edge distinction is reused verbatim; its
chain is not asserted to have groupoid restrictions. -/
theorem nonreconstructive_wholes :
    [GraphCut.B0,GraphCut.B1,GraphCut.B2,GraphCut.B3].map (GraphCut.colour GraphCut.principalGraph) =
      [GraphCut.B0,GraphCut.B1,GraphCut.B2,GraphCut.B3].map (GraphCut.colour GraphCut.alteredGraph) ∧
    GraphCut.colour GraphCut.principalGraph Finset.univ ≠ GraphCut.colour GraphCut.alteredGraph Finset.univ :=
  ⟨GraphCut.cross_edge_same_leaves,GraphCut.cross_edge_distinct_wholes⟩

/-- Exact imported separate noninvertible-interface witness, not a groupoid map. -/
theorem genuinely_noninvertible_interface : ¬ Function.Injective (fun _ : Bool => false) := by
  intro h
  have hh := h (a₁ := false) (a₂ := true) rfl
  contradiction


#print axioms nonidentity_automorphism
#print axioms noncommuting_changes
#print axioms repeated_nonempty
#print axioms mixed_frontier
#print axioms principal_blocks
#print axioms competing_groupings_same_full_cut
#print axioms distinct_refinements
#print axioms proper_occurrencewise_refinement
#print axioms principalCell
#print axioms actual_core_semantic_bridge
#print axioms parallel_semantic_witnesses
#print axioms nonglobular_factorization
#print axioms nonglobular_full_payload
#print axioms scalar_pair_distinct
#print axioms scalar_erasure_nonfaithful
#print axioms scalar_erasure_retains_partition
#print axioms nonreconstructive_wholes
#print axioms genuinely_noninvertible_interface
#print axioms E1FiniteExamples.nonidentity_factorization
#print axioms E1FiniteExamples.marked_binary_universal
#print axioms E1FiniteExamples.legitimate_nonuniversal
end E3FiniteExamples
