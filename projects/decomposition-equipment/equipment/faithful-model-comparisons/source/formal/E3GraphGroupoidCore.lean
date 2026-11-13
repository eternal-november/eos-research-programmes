import GraphCutFragment
import WitnessedDecompositions.WeightInvariant
import WitnessedDecompositions.RefinementFunctoriality

/-! E3 checked core-facing instance, not a mechanization of the full equipment.
There are three distinct interfaces and S3 grades in EVERY vertical hom-set.
A full cell stores a canonical graph partition and additive ZMod 2 scalar.
The P adapter identifies additive ZMod 2 with Multiplicative (ZMod 2) in G(6,K,M).
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace E3GraphGroupoidCore
open WitnessedDecompositions
open GraphCoordinates

structure Interface where
  tag : Fin 3
  deriving DecidableEq
instance : OfNat Interface n := ⟨⟨OfNat.ofNat n⟩⟩
abbrev Grade := Equiv.Perm (Fin 3)
/-- The indiscrete groupoid with isotropy S3; grades are not endpoint inequalities. -/
abbrev Vertical (_a _b : Interface) := Grade
structure Horizontal (_a _b : Interface) where
  graph : GraphCut.GraphColour
  grade : Grade
  deriving DecidableEq
instance : Quiver Interface := ⟨Horizontal⟩

def pathGrade {a : Interface} : {b : Interface} → Quiver.Path a b → Grade
  | _, .nil => 1
  | _, .cons p H => H.grade * pathGrade p

def pathGraphs {a : Interface} : {b : Interface} → Quiver.Path a b → List GraphCut.GraphColour
  | _, .nil => []
  | _, .cons p H => pathGraphs p ++ [H.graph]

/-- The ambient representation is PROOF only. Data are canonical local blocks;
whole graph and the ordered original typed profile are retained externally. -/
structure Partition (inputs : List GraphCut.GraphColour) (whole : GraphCut.GraphColour) where
  blocks : List (List Nat)
  valid : ∃ (G : Graph) (s : Block) (bs : List Block),
    IsPartition s bs ∧ whole = GraphCut.colour G s ∧ inputs = bs.map (GraphCut.colour G) ∧
      blocks = bs.map (GraphCut.localBlock s)

@[ext] theorem Partition.ext {xs : List GraphCut.GraphColour} {G : GraphCut.GraphColour}
    {U V : Partition xs G} (h : U.blocks = V.blocks) : U = V := by
  cases U; cases V; cases h; rfl

structure Cell {a b c d : Interface} (p : Quiver.Path a b) (H : c ⟶ d)
    (f : Vertical a c) (g : Vertical b d) where
  cut : Partition (pathGraphs p) H.graph
  weight : ZMod 2
  square : g * pathGrade p = H.grade * f

@[ext] theorem Cell.ext {a b c d : Interface} {p : Quiver.Path a b} {H : c ⟶ d}
    {f : Vertical a c} {g : Vertical b d} {α β : Cell p H f g}
    (hu : α.cut.blocks = β.cut.blocks) (hm : α.weight = β.weight) : α = β := by
  cases α; cases β; dsimp at hu hm
  have h := Partition.ext hu
  cases h; cases hm; rfl

/-- Chosen cartesian restriction changes only the grade, not the whole graph. -/
def restrict {a b c d : Interface} (H : c ⟶ d)
    (f : Vertical a c) (g : Vertical b d) : a ⟶ b :=
  ⟨H.graph, g⁻¹ * H.grade * f⟩

theorem restriction_formula {a b c d : Interface} (H : c ⟶ d)
    (f : Vertical a c) (g : Vertical b d) :
    (restrict H f g).grade = g⁻¹ * H.grade * f := rfl

/-- All-arity cartesian factorization: no bound on path length, and no erasure
of either partition witness or scalar. Nil paths are included. -/
def restrictionEquiv {a b c d e z : Interface} (p : Quiver.Path a b) (H : e ⟶ z)
    (f : Vertical c e) (g : Vertical d z) (u : Vertical a c) (v : Vertical b d) :
    Cell p H (f * u) (g * v) ≃ Cell p (restrict H f g) u v where
  toFun α := ⟨α.cut, α.weight, by
    change v * pathGrade p = (g⁻¹ * H.grade * f) * u
    have h := congrArg (fun x : Grade => g⁻¹ * x) α.square
    simpa only [mul_assoc, inv_mul_cancel_left] using h⟩
  invFun β := ⟨β.cut, β.weight, by
    change (g * v) * pathGrade p = H.grade * (f * u)
    have h := congrArg (fun x : Grade => g * x) β.square
    simpa only [restrict, mul_assoc, mul_inv_cancel_left] using h⟩
  left_inv _ := Cell.ext rfl rfl
  right_inv _ := Cell.ext rfl rfl

theorem restriction_retains_cut {a b c d e z : Interface} (p : Quiver.Path a b)
    (H : e ⟶ z) (f : Vertical c e) (g : Vertical d z)
    (u : Vertical a c) (v : Vertical b d) (α : Cell p H (f*u) (g*v)) :
    (restrictionEquiv p H f g u v α).cut.blocks = α.cut.blocks ∧
    (restrictionEquiv p H f g u v α).weight = α.weight := ⟨rfl,rfl⟩

/-- Composition with the chosen cartesian cell is the inverse operation on
complete witnesses. Its scalar is zero and singleton block is neutral (P adapter). -/
def restrictionCompose {a b c d e z : Interface} (p : Quiver.Path a b) (H : e ⟶ z)
    (f : Vertical c e) (g : Vertical d z) (u : Vertical a c) (v : Vertical b d) :=
  (restrictionEquiv p H f g u v).symm

theorem restriction_factorization {a b c d e z : Interface} (p : Quiver.Path a b)
    (H : e ⟶ z) (f : Vertical c e) (g : Vertical d z)
    (u : Vertical a c) (v : Vertical b d) (α : Cell p H (f*u) (g*v)) :
    restrictionCompose p H f g u v (restrictionEquiv p H f g u v α) = α :=
  (restrictionEquiv p H f g u v).symm_apply_apply α

theorem restriction_unique {a b c d e z : Interface} (p : Quiver.Path a b)
    (H : e ⟶ z) (f : Vertical c e) (g : Vertical d z)
    (u : Vertical a c) (v : Vertical b d) (α : Cell p H (f*u) (g*v))
    (β : Cell p (restrict H f g) u v)
    (hb : restrictionCompose p H f g u v β = α) :
    β = restrictionEquiv p H f g u v α := by
  rw [← hb]
  exact ((restrictionEquiv p H f g u v).apply_symm_apply β).symm

theorem restrict_identity {a b : Interface} (H : a ⟶ b) : restrict H 1 1 = H := by
  cases H; simp [restrict]

theorem restrict_composite {a b c d e z : Interface} (H : e ⟶ z)
    (f : Vertical c e) (g : Vertical d z) (u : Vertical a c) (v : Vertical b d) :
    restrict (a := a) (b := b) (restrict (a := c) (b := d) H f g) u v = restrict (a := a) (b := b) H (f*u) (g*v) := by
  simp only [restrict, mul_inv_rev, mul_assoc]

def binaryPartition (g : GraphCut.BinaryCut) : Partition [g.left,g.right] g.whole :=
  ⟨[g.leftBlock,g.rightBlock], by
    obtain ⟨G,s,u,v,hp,hw,hl,hr,hul,hvr⟩ := g.valid
    exact ⟨G,s,[u,v],hp,hw,by simp [hl,hr],by simp [hul,hvr]⟩⟩

/-- Only semantically valid binary cuts, arbitrary S3 grades and scalars. The
old C1 chain endpoints are NOT carried as hidden generator labels. -/
structure Binary where
  a : Interface
  b : Interface
  c : Interface
  whole : GraphCut.GraphColour
  left : GraphCut.GraphColour
  right : GraphCut.GraphColour
  cut : Partition [left,right] whole
  first : Grade
  second : Grade
  weight : ZMod 2

def ofC1 (g : GraphCut.BinaryCut) (first second : Grade) (weight : ZMod 2 := 0) : Binary :=
  ⟨⟨g.a.value⟩,⟨g.b.value⟩,⟨g.c.value⟩,g.whole,g.left,g.right,binaryPartition g,first,second,weight⟩

def signature : Signature Interface where
  Generator := Binary ⊕ (Interface × ZMod 2)
  source | .inl g => g.a | .inr u => u.1
  target | .inl g => g.c | .inr u => u.1
  input
    | .inl g => (Quiver.Path.nil.cons (⟨g.left,g.first⟩ : Horizontal g.a g.b)).cons
        (⟨g.right,g.second⟩ : Horizontal g.b g.c)
    | .inr _ => .nil
  output
    | .inl g => ⟨g.whole,g.second*g.first⟩
    | .inr _ => ⟨GraphCut.emptyColour,1⟩

abbrev CutTree := Tree signature
abbrev coreCalc : Calc Interface := Tree.freeCalc signature

def generatorWeight : signature.Generator → Nat
  | .inl g => g.weight.val
  | .inr u => u.2.val

def generatorBlock : (g : signature.Generator) → Path.Slot (signature.input g) → List Nat
  | .inl _g, .inl (.inl i) => nomatch i
  | .inl g, .inl (.inr ()) => g.cut.blocks[0]?.getD []
  | .inl g, .inr () => g.cut.blocks[1]?.getD []
  | .inr _, i => nomatch i

def treeBlocks : {c : Component Interface} → CutTree c → List (List Nat)
  | c, .leaf _ => [List.range c.edge.graph.val.1]
  | _, .node g children => Path.collect (signature.input g)
      (fun i => (treeBlocks (children i)).map (GraphCut.liftBlock (generatorBlock g i)))

structure FullCut (a b : Interface) where
  whole : GraphCut.GraphColour
  profile : Quiver.Path a b
  blocks : List (List Nat)
  weight : ZMod 2

def evaluate {c : Component Interface} (t : CutTree c) : FullCut c.source c.target :=
  ⟨c.edge.graph,Tree.frontier t,treeBlocks t,(Tree.weight generatorWeight t : ZMod 2)⟩

theorem evaluation_profile {c : Component Interface} (t : CutTree c) :
    (evaluate t).profile = coreCalc.profile t := rfl

theorem evaluation_graft_profile {c : Component Interface} (t : CutTree c)
    (f : Tree.Substitution t) :
    (evaluate (Tree.graft t f)).profile = Tree.substitutionFrontier t f :=
  Tree.frontier_graft t f

theorem scalar_substitution {c : Component Interface} (t : CutTree c)
    (f : (Tree.collection signature).Family (Tree.frontier t)) :
    (evaluate (Tree.profileGraft t f)).weight = (evaluate t).weight +
      (Path.sum (Tree.frontier t) (fun i => Tree.weight generatorWeight (f i)) : ZMod 2) := by
  change (Tree.weight generatorWeight (Tree.profileGraft t f) : ZMod 2) = _
  rw [Tree.weight_profileGraft, Nat.cast_add]
  rfl

theorem evaluation_identity {c : Component Interface} (t : CutTree c) :
    evaluate (Tree.graft t (Tree.identity t)) = evaluate t := by rw [Tree.graft_identity]

theorem evaluation_associative {c : Component Interface} (t : CutTree c)
    (f : Tree.Substitution t) (h : Tree.Substitution (Tree.graft t f)) :
    evaluate (Tree.graft (Tree.graft t f) h) = evaluate (Tree.graft t (Tree.compose t f h)) := by
  rw [Tree.graft_assoc]

/-- The primitive semantic bridge is checked against actual Cell, not merely a
record with matching labels. Arbitrary binary partitions and finite scalars survive. -/
def primitiveCell (g : signature.Generator) :
    Cell (signature.input g) (signature.output g) 1 1 := by
  cases g with
  | inl b =>
    refine ⟨b.cut,b.weight,?_⟩
    simp [signature,pathGrade]
  | inr u =>
    refine ⟨⟨[],?_⟩,u.2,?_⟩
    · exact ⟨sixGraph,∅,[],partition_empty,rfl,rfl,rfl⟩
    · simp [signature,pathGrade]

theorem primitive_bridge_blocks (b : Binary) :
    (primitiveCell (.inl b)).cut.blocks = b.cut.blocks := rfl

theorem primitive_bridge_scalar (b : Binary) :
    (primitiveCell (.inl b)).weight = b.weight := rfl

/-- A genuine, generally NONFAITHFUL original-core morphism: erase each
primitive's scalar while keeping its full graph cut and original typed profile. -/
def eraseGenerator : signature.Generator → signature.Generator
  | .inl b => .inl {b with weight := 0}
  | .inr u => .inr (u.1,0)

def eraseAssignment : signature.Assignment coreCalc := by
  intro g
  cases g with
  | inl b => exact ⟨Tree.corolla (S := signature) (eraseGenerator (.inl b)),
      Tree.frontier_corolla _⟩
  | inr u => exact ⟨Tree.corolla (S := signature) (eraseGenerator (.inr u)),
      Tree.frontier_corolla _⟩

def eraseScalar : Calc.Hom coreCalc coreCalc := Tree.extend coreCalc eraseAssignment

theorem eraseScalar_profile {c : Component Interface} (t : CutTree c) :
    (evaluate (eraseScalar.map t)).profile = (evaluate t).profile :=
  eraseScalar.profile_map t

/-- B2's genuine occurrence-indexed refinement functor induced by that map.
It is not declared faithful: the scalar pair in E3FiniteExamples is collapsed. -/
def eraseRefinement (c : Component Interface) := SemanticRefinement.functor eraseScalar c

#print axioms restriction_formula
#print axioms restrictionEquiv
#print axioms restriction_retains_cut
#print axioms restriction_factorization
#print axioms restriction_unique
#print axioms restrict_identity
#print axioms restrict_composite
#print axioms binaryPartition
#print axioms coreCalc
#print axioms evaluation_profile
#print axioms evaluation_graft_profile
#print axioms scalar_substitution
#print axioms evaluation_identity
#print axioms evaluation_associative
#print axioms primitiveCell
#print axioms primitive_bridge_blocks
#print axioms primitive_bridge_scalar
#print axioms eraseScalar
#print axioms eraseScalar_profile
#print axioms eraseRefinement
end E3GraphGroupoidCore
