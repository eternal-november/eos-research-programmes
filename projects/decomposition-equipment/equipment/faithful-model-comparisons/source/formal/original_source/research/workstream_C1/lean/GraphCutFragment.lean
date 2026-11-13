import WitnessedDecompositions.Examples
import WitnessedDecompositions.FreeCalculus
import WitnessedDecompositions.PresentedCalculus
import GraphCoordinates

/-! C1 local fragment, contract v0.1 hash
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
This file constructs real graph-coloured A trees and their full cut evaluation.
All-size semantic Calc laws are separately P; this is not a claim of C5/F2. -/
set_option backward.isDefEq.respectTransparency false
namespace WitnessedDecompositions.GraphCut
open GraphCoordinates

/-- An arbitrary finite ordered simple graph; no six-vertex restriction here. -/
structure OrderedGraph (n : Nat) where
  adjacent : Fin n → Fin n → Bool
  symmetric : ∀ i j, adjacent i j = adjacent j i
  loopless : ∀ i, adjacent i i = false

/-- Restriction is pullback along the declared increasing inclusion. -/
def restrict {n m : Nat} (G : OrderedGraph n) (e : Fin m ↪o Fin n) : OrderedGraph m where
  adjacent i j := G.adjacent (e i) (e j)
  symmetric _ _ := G.symmetric _ _
  loopless _ := G.loopless _

/-- The generic graph restriction law is literal equality of full adjacency. -/
theorem restrict_trans {n m k : Nat} (G : OrderedGraph n)
    (e : Fin m ↪o Fin n) (f : Fin k ↪o Fin m) :
    restrict (restrict G e) f = restrict G (f.trans e) := rfl

/-- Certified graph codes: exactly induced ordered simple graphs of size ≤6.
The existential is proof-only; no ambient location is retained as a colour. -/
abbrev GraphColour := {c : Nat × List Bool // ∃ G : Graph, ∃ s : Block, c = graphCode G s}

def colour (G : Graph) (s : Block) : GraphColour :=
  ⟨graphCode G s, G, s, rfl⟩

structure Interface where
  value : Fin 3
  deriving DecidableEq

instance : OfNat Interface n := ⟨⟨OfNat.ofNat n⟩⟩

/-- The grade is the actual arrow in the three-object chain. -/
structure GraphArrow (a b : Interface) where
  graph : GraphColour
  grade : a.value ≤ b.value
  deriving DecidableEq

instance : Quiver Interface := ⟨GraphArrow⟩

def edge (G : Graph) (s : Block) (a b : Interface) (h : a.value ≤ b.value) : a ⟶ b :=
  ⟨colour G s, h⟩

def component (G : Graph) (s : Block) (a b : Interface) (h : a.value ≤ b.value) : Component Interface :=
  ⟨a, b, edge G s a b h⟩

/-- Canonical coordinates of a subblock; all indices are ranks in the support. -/
def localBlock (s b : Block) : List Nat :=
  ((enumerate s).zipIdx.filter fun vi => vi.1 ∈ b).map Prod.snd

/-- Data of a binary cut in canonical whole coordinates. The proof asserts its
actual graph meaning but does not add ambient labels to the witness. -/
structure BinaryCut where
  a : Interface
  b : Interface
  c : Interface
  whole : GraphColour
  left : GraphColour
  right : GraphColour
  leftBlock : List Nat
  rightBlock : List Nat
  ab : a.value ≤ b.value
  bc : b.value ≤ c.value
  valid : ∃ G : Graph, ∃ s u v : Block,
    IsPartition s [u,v] ∧ whole = colour G s ∧ left = colour G u ∧
      right = colour G v ∧ leftBlock = localBlock s u ∧ rightBlock = localBlock s v

/-- Construct a cut without adding its coordinate representation to its data. -/
def binaryCut (G : Graph) (s u v : Block) (hp : IsPartition s [u,v])
    (a b c : Interface) (hab : a.value ≤ b.value) (hbc : b.value ≤ c.value) : BinaryCut where
  a := a; b := b; c := c
  whole := colour G s; left := colour G u; right := colour G v
  leftBlock := localBlock s u; rightBlock := localBlock s v
  ab := hab; bc := hbc
  valid := ⟨G,s,u,v,hp,rfl,rfl,rfl,rfl,rfl⟩

def emptyColour : GraphColour := colour sixGraph ∅

/-- Binary cuts and designated nullaries; no arbitrary loop nullary is added. -/
def cutSignature : Signature Interface where
  Generator := BinaryCut ⊕ Interface
  source | .inl g => g.a | .inr a => a
  target | .inl g => g.c | .inr a => a
  input
    | .inl g => (Quiver.Path.nil.cons (⟨g.left,g.ab⟩ : GraphArrow g.a g.b)).cons
        (⟨g.right,g.bc⟩ : GraphArrow g.b g.c)
    | .inr _ => Quiver.Path.nil
  output
    | .inl g => ⟨g.whole, le_trans g.ab g.bc⟩
    | .inr _ => ⟨emptyColour, le_rfl⟩

abbrev CutTree := Tree cutSignature

def cut {g : BinaryCut}
    (x : CutTree ⟨g.a,g.b,⟨g.left,g.ab⟩⟩)
    (y : CutTree ⟨g.b,g.c,⟨g.right,g.bc⟩⟩) :
    CutTree ⟨g.a,g.c,⟨g.whole,le_trans g.ab g.bc⟩⟩ :=
  Tree.node (S := cutSignature) (.inl g) (Examples.binaryChildren x y)

/-- Local-to-parent lifting, with the finite validity proof supplied by the
cut generator. Invalid out-of-range ranks cannot occur for valid trees. -/
def liftBlock (parent child : List Nat) : List Nat :=
  child.map (fun i => parent[i]?.getD 0)

def generatorBlock : (g : cutSignature.Generator) → Path.Slot (cutSignature.input g) → List Nat
  | .inl _g, .inl (.inl i) => nomatch i
  | .inl g, .inl (.inr ()) => g.leftBlock
  | .inl g, .inr () => g.rightBlock
  | .inr _, i => nomatch i

/-- Actual cut evaluation: refinement lifts each child's own local coordinates.
This retains occurrence order even when child component colours are identical. -/
def treeBlocks : {c : Component Interface} → CutTree c → List (List Nat)
  | c, .leaf _ => [List.range c.edge.graph.val.1]
  | _, .node g children => Path.collect (cutSignature.input g)
      (fun i => (treeBlocks (children i)).map (liftBlock (generatorBlock g i)))

structure FullCut (a b : Interface) where
  whole : GraphColour
  profile : Quiver.Path a b
  blocks : List (List Nat)

/-- The whole graph is explicitly stored, not inferred from its pieces. -/
def graphEvaluate {c : Component Interface} (t : CutTree c) : FullCut c.source c.target :=
  ⟨c.edge.graph, Tree.frontier t, treeBlocks t⟩

/-- The new semantics uses the actual A frontier, not an untyped substitute. -/
theorem graphEvaluate_profile {c : Component Interface} (t : CutTree c) :
    (graphEvaluate t).profile = Tree.frontier t := rfl

/-- The exact accepted A occurrence-graft law applies to these graph trees. -/
theorem graph_graft_frontier {c : Component Interface} (t : CutTree c) (f : Tree.Substitution t) :
    (graphEvaluate (Tree.graft t f)).profile = Tree.substitutionFrontier t f :=
  Tree.frontier_graft t f

/-! Frozen six-vertex certificate. -/
def principalGraph : Graph where
  edge i j := decide ((i.val,j.val) ∈
    [(0,1),(1,0),(1,2),(2,1),(1,3),(3,1),(2,4),(4,2),(3,4),(4,3),(4,5),(5,4)])
  symmetric := by decide
  loopless := by decide

def alteredGraph : Graph where
  edge i j := principalGraph.edge i j || decide ((i.val,j.val) ∈ [(0,5),(5,0)])
  symmetric := by decide
  loopless := by decide

def B0 : Block := {0}
def B1 : Block := {1,3}
def B2 : Block := {2,4}
def B3 : Block := {5}

def c0 := component principalGraph B0 0 1 (by decide)
def c1 := component principalGraph B1 1 1 (by decide)
def c2 := component principalGraph B2 1 1 (by decide)
def c3 := component principalGraph B3 1 2 (by decide)
def whole := component principalGraph Finset.univ 0 2 (by decide)

theorem repeated_nonempty_component : B1.Nonempty ∧ B2.Nonempty ∧ c1 = c2 := by
  refine ⟨by decide, by decide, ?_⟩
  unfold c1 c2 component edge
  congr 2

def split01 := binaryCut principalGraph (B0 ∪ B1) B0 B1 (by decide) 0 1 1 (by decide) (by decide)
def split23 := binaryCut principalGraph (B2 ∪ B3) B2 B3 (by decide) 1 1 2 (by decide) (by decide)
def split0123 := binaryCut principalGraph Finset.univ (B0 ∪ B1) (B2 ∪ B3) (by decide) 0 1 2 (by decide) (by decide)
def split123 := binaryCut principalGraph (B1 ∪ (B2 ∪ B3)) B1 (B2 ∪ B3) (by decide) 1 1 2 (by decide) (by decide)
def split0_123 := binaryCut principalGraph Finset.univ B0 (B1 ∪ (B2 ∪ B3)) (by decide) 0 1 2 (by decide) (by decide)

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

theorem mixed_four_frontier : Tree.frontier leftGrouped = flatProfile ∧
    Tree.frontier rightGrouped = flatProfile := ⟨rfl,rfl⟩

theorem competing_groupings_same_cut : graphEvaluate leftGrouped = graphEvaluate rightGrouped := by
  rfl

theorem principal_flat_blocks : (graphEvaluate leftGrouped).blocks = [[0],[1,3],[2,4],[5]] := by
  decide


/-- Different primitive root cuts remain distinct presentation data. -/
theorem competing_groupings_distinct_trees : leftGrouped ≠ rightGrouped := by
  intro h
  have hs := congrArg (fun t => (Tree.generators t).map fun g =>
    match g with | .inl b => b.leftBlock | .inr _ => []) h
  have hn : (Tree.generators leftGrouped).map (fun g =>
    match g with | .inl b => b.leftBlock | .inr _ => []) ≠
      (Tree.generators rightGrouped).map (fun g =>
    match g with | .inl b => b.leftBlock | .inr _ => []) := by decide
  exact hn hs

/-- Supply an independent graft at each of a binary node's child subtrees. -/
def cutForest {g : BinaryCut}
    (x : CutTree ⟨g.a,g.b,⟨g.left,g.ab⟩⟩)
    (y : CutTree ⟨g.b,g.c,⟨g.right,g.bc⟩⟩)
    (fx : Tree.Substitution x) (fy : Tree.Substitution y) :
    Tree.Substitution (cut (g := g) x y)
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => fx
  | .inr () => fy

def splitFirst := binaryCut principalGraph B1 {1} {3} (by decide)
  1 1 1 (by decide) (by decide)
def splitSecond := binaryCut principalGraph B2 {4} {2} (by decide)
  1 1 1 (by decide) (by decide)

def firstReplacement : CutTree c1 := Tree.corolla (S := cutSignature) (.inl splitFirst)
def secondReplacement : CutTree c2 := Tree.corolla (S := cutSignature) (.inl splitSecond)

theorem repeated_refinements_distinct :
    (graphEvaluate firstReplacement).whole = (graphEvaluate secondReplacement).whole ∧
    (graphEvaluate firstReplacement).profile = (graphEvaluate secondReplacement).profile ∧
    (graphEvaluate firstReplacement).blocks = [[0],[1]] ∧
    (graphEvaluate secondReplacement).blocks = [[1],[0]] ∧
    graphEvaluate firstReplacement ≠ graphEvaluate secondReplacement := by
  refine ⟨rfl,rfl,by decide,by decide,?_⟩
  intro h
  have hh := congrArg FullCut.blocks h
  have : (graphEvaluate firstReplacement).blocks ≠ (graphEvaluate secondReplacement).blocks := by decide
  exact this hh

/-- The two equal middle colours receive distinct binary replacement witnesses.
The data are indexed by actual structural occurrences, never by colour equality. -/
def differentForest : Tree.Substitution rightGrouped :=
  cutForest (g := split0_123) (.leaf c0)
    (cut (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3)))
    (.leaf c0)
    (cutForest (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3))
      firstReplacement
      (cutForest (g := split23) (.leaf c2) (.leaf c3) secondReplacement (.leaf c3)))

def refined : CutTree whole := Tree.graft rightGrouped differentForest

theorem occurrencewise_refinement_certificate :
    (graphEvaluate refined).whole = colour principalGraph Finset.univ ∧
    (graphEvaluate refined).blocks = [[0],[1],[3],[4],[2],[5]] ∧
    (graphEvaluate refined).profile.length = 6 := by
  exact ⟨rfl,by decide,rfl⟩

/-- This is the ordinary A graft, hence also the accepted free Calc operation. -/
theorem occurrencewise_graft_is_A_graft : refined = Tree.graft rightGrouped differentForest := rfl

theorem graph_graft_identity {c : Component Interface} (t : CutTree c) :
    graphEvaluate (Tree.graft t (Tree.identity t)) = graphEvaluate t := by
  rw [Tree.graft_identity]

theorem graph_graft_assoc {c : Component Interface} (t : CutTree c)
    (f : Tree.Substitution t) (h : Tree.Substitution (Tree.graft t f)) :
    graphEvaluate (Tree.graft (Tree.graft t f) h) =
      graphEvaluate (Tree.graft t (Tree.compose t f h)) := by
  rw [Tree.graft_assoc]

/-- Same leaves do not erase the retained cross-block edge of the whole. -/
theorem cross_edge_same_leaves :
    [B0,B1,B2,B3].map (fun b => colour principalGraph b) =
      [B0,B1,B2,B3].map (fun b => colour alteredGraph b) := by
  decide

theorem cross_edge_distinct_wholes :
    colour principalGraph Finset.univ ≠ colour alteredGraph Finset.univ := by decide

/-- Binary regrouping in the altered whole, with all internal restrictions real. -/
def alteredSplit01 := binaryCut alteredGraph (B0 ∪ B1) B0 B1 (by decide) 0 1 1 (by decide) (by decide)
def alteredSplit23 := binaryCut alteredGraph (B2 ∪ B3) B2 B3 (by decide) 1 1 2 (by decide) (by decide)
def alteredSplit0123 := binaryCut alteredGraph Finset.univ (B0 ∪ B1) (B2 ∪ B3) (by decide) 0 1 2 (by decide) (by decide)
def alteredWhole := component alteredGraph Finset.univ 0 2 (by decide)

def alteredTree : CutTree alteredWhole :=
  cut (g := alteredSplit0123)
    (cut (g := alteredSplit01)
      (.leaf (component alteredGraph B0 0 1 (by decide)))
      (.leaf (component alteredGraph B1 1 1 (by decide))))
    (cut (g := alteredSplit23)
      (.leaf (component alteredGraph B2 1 1 (by decide)))
      (.leaf (component alteredGraph B3 1 2 (by decide))))

theorem cross_edge_same_typed_profile :
    (graphEvaluate leftGrouped).profile = (graphEvaluate alteredTree).profile := rfl

theorem cross_edge_distinct_full_witnesses :
    graphEvaluate leftGrouped ≠ graphEvaluate alteredTree := by
  intro h
  exact cross_edge_distinct_wholes (congrArg FullCut.whole h)

/-- The identity tree on the empty graph is one leaf, not a zero-leaf unit. -/
def emptyComponent : Component Interface := ⟨1,1,⟨emptyColour,le_rfl⟩⟩
def emptyIdentity : CutTree emptyComponent := Tree.leaf emptyComponent
def nullary : CutTree emptyComponent := Tree.corolla (S := cutSignature) (.inr 1)

theorem empty_leaf_not_nullary :
    (graphEvaluate emptyIdentity).blocks = [[]] ∧
    (graphEvaluate nullary).blocks = [] ∧
    (graphEvaluate emptyIdentity).profile.length = 1 ∧
    (graphEvaluate nullary).profile.length = 0 ∧
    graphEvaluate emptyIdentity ≠ graphEvaluate nullary := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro h
  have hh := congrArg FullCut.blocks h
  cases hh

/-- Ill-composable graph interfaces are rejected by the same A constructor. -/
example : True := by
  fail_if_success have bad := cut (g := split01) (.leaf c0) (.leaf c0)
  trivial



/-- Executable partition check in canonical whole coordinates, with multiplicity
retained: coverage alone would accept duplicated vertices and is insufficient. -/
def IsLocalPartition (n : Nat) (bs : List (List Nat)) : Prop :=
  bs.flatten.Nodup ∧ ∀ i : Nat, i ∈ bs.flatten ↔ i < n

/-- Kernel verification of the concrete principal and refined partitions. -/
theorem principal_partition_valid :
    GraphCoordinates.IsPartition Finset.univ [B0,B1,B2,B3] := by decide

theorem principal_local_coordinates :
    split0123.leftBlock = [0,1,3] ∧ split0123.rightBlock = [2,4,5] ∧
    split123.leftBlock = [0,2] ∧ split123.rightBlock = [1,3,4] ∧
    splitFirst.leftBlock = [0] ∧ splitSecond.leftBlock = [1] := by decide

theorem refined_partition_valid :
    IsLocalPartition 6 (graphEvaluate refined).blocks := by
  change ([0,1,3,4,2,5] : List Nat).Nodup ∧
    ∀ i : Nat, i ∈ ([0,1,3,4,2,5] : List Nat) ↔ i < 6
  constructor
  · decide
  · intro i
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-! The actual A3 quotient, on one explicitly declared local rotation. -/
def c23 := component principalGraph (B2 ∪ B3) 1 2 (by decide)
def rotationLeft : CutTree whole :=
  cut (g := split0123) (cut (g := split01) (.leaf c0) (.leaf c1)) (.leaf c23)
def rotationRight : CutTree whole :=
  cut (g := split0_123) (.leaf c0) (cut (g := split123) (.leaf c1) (.leaf c23))
def tripleProfile : Quiver.Path (V := Interface) 0 2 :=
  ((Quiver.Path.nil.cons c0.edge).cons c1.edge).cons c23.edge

def rotationLeftOp : Tree.Operation (S := cutSignature) whole tripleProfile := ⟨rotationLeft,rfl⟩
def rotationRightOp : Tree.Operation (S := cutSignature) whole tripleProfile := ⟨rotationRight,rfl⟩

/-- This relation contains the named local parallel rotation only, not every
observed model equality. Its least substitution closure is the accepted A3 one. -/
inductive Declared : ∀ (c : Component Interface) (p : Quiver.Path c.source c.target),
    Tree.Operation (S := cutSignature) c p → Tree.Operation (S := cutSignature) c p → Prop where
  | rotation : Declared whole tripleProfile rotationLeftOp rotationRightOp

def equations : Presentation.Equations cutSignature := Declared

theorem rotation_derivable : Presentation.Derives cutSignature equations rotationLeft rotationRight :=
  Presentation.Derives.equation rotationLeftOp rotationRightOp Declared.rotation

/-- The local equation is verified against FULL graph witnesses. -/
theorem declared_full_cut_sound :
    ∀ c p (t u : Tree.Operation (S := cutSignature) c p), equations c p t u →
      graphEvaluate t.val = graphEvaluate u.val := by
  intro c p t u h
  cases h
  rfl

def rotationForest : (i : Path.Slot tripleProfile) → CutTree (Path.componentAt tripleProfile i)
  | .inl (.inl (.inl i)) => nomatch i
  | .inl (.inl (.inr ())) => .leaf c0
  | .inl (.inr ()) => .leaf c1
  | .inr () => cut (g := split23) (.leaf c2) (.leaf c3)

def rotationProfiles (i : Path.Slot tripleProfile) := Tree.frontier (rotationForest i)
def rotationOperations (i : Path.Slot tripleProfile) :
    Tree.Operation (S := cutSignature) (Path.componentAt tripleProfile i) (rotationProfiles i) :=
  ⟨rotationForest i,rfl⟩

/-- A3 substitution actually converts the local rotation into the four-leaf
certificate. This is not an unrelated use of the imported theorem name. -/
theorem competing_groupings_derivable :
    Presentation.Derives cutSignature equations leftGrouped rightGrouped := by
  have hl : (Tree.substituteOperation rotationLeftOp rotationProfiles rotationOperations).val = leftGrouped := by
    change Tree.node _ _ = Tree.node _ _
    congr 1
    funext i
    rcases i with (i | ⟨⟩) | ⟨⟩
    · cases i
    · change Tree.node _ _ = Tree.node _ _
      congr 1
      funext j
      rcases j with (j | ⟨⟩) | ⟨⟩
      · cases j
      · rfl
      · rfl
    · rfl
  have hr : (Tree.substituteOperation rotationRightOp rotationProfiles rotationOperations).val = rightGrouped := by
    change Tree.node _ _ = Tree.node _ _
    congr 1
    funext i
    rcases i with (i | ⟨⟩) | ⟨⟩
    · cases i
    · rfl
    · change Tree.node _ _ = Tree.node _ _
      congr 1
      funext j
      rcases j with (j | ⟨⟩) | ⟨⟩
      · cases j
      · rfl
      · rfl
  have h := Presentation.Derives.substitute rotationLeftOp rotationRightOp rotation_derivable
    rotationProfiles rotationOperations rotationOperations (fun i => Presentation.Derives.refl _)
  rw [hl, hr] at h
  exact h

theorem competing_groupings_equal_in_A3_quotient :
    (Presentation.projection equations).map leftGrouped =
      (Presentation.projection equations).map rightGrouped :=
  (Presentation.quotient_eq_iff equations leftGrouped rightGrouped).2 competing_groupings_derivable



/-- A deliberately colour-keyed forest must reuse the first replacement on
both identical middle colours. The resulting cut is NOT the requested cut. -/
def collapsedForest : Tree.Substitution rightGrouped :=
  cutForest (g := split0_123) (.leaf c0)
    (cut (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3)))
    (.leaf c0)
    (cutForest (g := split123) (.leaf c1) (cut (g := split23) (.leaf c2) (.leaf c3))
      firstReplacement
      (cutForest (g := split23) (.leaf c2) (.leaf c3) firstReplacement (.leaf c3)))

theorem colour_keyed_mutation_rejected :
    (graphEvaluate (Tree.graft rightGrouped collapsedForest)).blocks = [[0],[1],[3],[2],[4],[5]] ∧
    graphEvaluate (Tree.graft rightGrouped collapsedForest) ≠ graphEvaluate refined := by
  refine ⟨by decide,?_⟩
  intro h
  have hh := congrArg FullCut.blocks h
  have : (graphEvaluate (Tree.graft rightGrouped collapsedForest)).blocks ≠
      (graphEvaluate refined).blocks := by decide
  exact this hh

/-- A wrong evaluator that forgets each cut's local-to-parent inclusion. -/
def treeBlocksWithoutLift : {c : Component Interface} → CutTree c → List (List Nat)
  | c, .leaf _ => [List.range c.edge.graph.val.1]
  | _, .node g children => Path.collect (cutSignature.input g)
      (fun i => treeBlocksWithoutLift (children i))

theorem coordinate_erasure_mutation_rejected :
    treeBlocksWithoutLift leftGrouped ≠ (graphEvaluate leftGrouped).blocks := by decide

theorem invalid_partition_rejected :
    ¬ GraphCoordinates.IsPartition Finset.univ [B0,B1,B1,B3] ∧
    ¬ GraphCoordinates.IsPartition Finset.univ [B0,B1,B3] := by decide

/-- Unequal-endpoint nullaries cannot be supplied by the graph signature. -/
example : True := by
  fail_if_success have bad : CutTree c0 := Tree.corolla (S := cutSignature) (.inr 0)
  trivial


end WitnessedDecompositions.GraphCut
