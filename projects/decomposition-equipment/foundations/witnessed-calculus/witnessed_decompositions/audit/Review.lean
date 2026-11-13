import WitnessedDecompositions.Core

open WitnessedDecompositions

namespace IndependentAudit

-- Four genuinely distinct interfaces and a graph with no arbitrary filler edges.
inductive Interface where
  | a | b | c | d
  deriving DecidableEq

inductive Edge : Interface → Interface → Type where
  | x : Edge .a .b
  | y : Edge .b .c
  | z : Edge .c .d
  | xy : Edge .a .c
  | yz : Edge .b .d
  | xyz : Edge .a .d

instance : Quiver Interface where Hom := Edge

inductive Gen where
  | xy | yz | left | right
  deriving DecidableEq

def S : Signature Interface where
  Generator := Gen
  source
    | .xy => .a
    | .yz => .b
    | .left | .right => .a
  target
    | .xy => .c
    | .yz | .left | .right => .d
  input
    | .xy => (Quiver.Path.nil.cons Edge.x).cons Edge.y
    | .yz => (Quiver.Path.nil.cons Edge.y).cons Edge.z
    | .left => (Quiver.Path.nil.cons Edge.xy).cons Edge.z
    | .right => (Quiver.Path.nil.cons Edge.x).cons Edge.yz
  output
    | .xy => Edge.xy
    | .yz => Edge.yz
    | .left | .right => Edge.xyz

def corolla (g : Gen) : Tree S (S.result g) :=
  Tree.node (S := S) g (fun i => .leaf (S.argument g i))

def left : Tree S ⟨.a, .d, Edge.xyz⟩ :=
  Tree.node (S := S) Gen.left (fun
    | .inl (.inl i) => nomatch i
    | .inl (.inr ()) => corolla .xy
    | .inr () => Tree.leaf (S := S) ⟨Interface.c, Interface.d, Edge.z⟩)

def right : Tree S ⟨.a, .d, Edge.xyz⟩ :=
  Tree.node (S := S) Gen.right (fun
    | .inl (.inl i) => nomatch i
    | .inl (.inr ()) => Tree.leaf (S := S) ⟨Interface.a, Interface.b, Edge.x⟩
    | .inr () => corolla .yz)

def root {c : Component Interface} : Tree S c → Option Gen
  | .leaf _ => none
  | .node g _ => some g

theorem genuinely_distinct : left ≠ right := by
  intro h
  have h' := congrArg root h
  cases h'

theorem same_typed_flattening : Tree.frontier left = Tree.frontier right := rfl

theorem correct_three_edge_frontier :
    Tree.frontier left = ((Quiver.Path.nil.cons Edge.x).cons Edge.y).cons Edge.z := rfl

theorem actual_semantic_equality :
    Algebra.evaluate (Algebra.flattening (S := S)) (fun c => c.edge.toPath) left =
    Algebra.evaluate (Algebra.flattening (S := S)) (fun c => c.edge.toPath) right := rfl

-- No middle interface can silently be dropped: the graph has no a-to-c edge
-- equal to x, and the constructor cannot concatenate x directly with z.
example : Quiver.Path Interface.a Interface.d := by
  fail_if_success exact (Quiver.Path.nil.cons Edge.x).cons Edge.z
  exact ((Quiver.Path.nil.cons Edge.x).cons Edge.y).cons Edge.z

example : Tree S ⟨.a, .b, Edge.x⟩ := by
  fail_if_success exact (Tree.leaf (S := S) ⟨.c, .d, Edge.z⟩)
  exact .leaf _

#print axioms Tree.graft_leaf
#print axioms Tree.graft_identity
#print axioms Tree.graft_assoc
#print axioms Tree.substitutionEquiv
#print axioms Tree.frontier_components
#print axioms Tree.leaves_graft
#print axioms Tree.frontier_graft
#print axioms Signature.nullary_is_loop
#print axioms Algebra.evaluate_presentation
#print axioms Algebra.evaluate_unique
#print axioms genuinely_distinct
#print axioms same_typed_flattening

namespace Loop

instance : Quiver Unit where Hom _ _ := Unit

def color : Component Unit := ⟨(), (), ()⟩

inductive Witness where
  | fork | tag | erase

def one : Quiver.Path (V := Unit) () () := Quiver.Path.nil.cons ()

def signature : Signature Unit where
  Generator := Witness
  source _ := ()
  target _ := ()
  input
    | .fork => one.cons ()
    | .tag => one
    | .erase => Quiver.Path.nil
  output _ := ()

def primitive (g : Witness) : Tree signature color :=
  Tree.node (S := signature) g (fun i => .leaf (signature.argument g i))

def pair := primitive Witness.fork
def tag := primitive Witness.tag
def empty := primitive Witness.erase

def first : Tree.Substitution pair := fun
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => empty
  | .inr () => tag

-- Repeated identical components get different replacements, one of which is nullary.
theorem independent_replacements :
    (Tree.graft pair first).leaves = [color] := rfl

def reversed : Tree.Substitution pair := fun
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => tag
  | .inr () => empty

def witnessList {c : Component Unit} : Tree signature c → List Witness
  | .leaf _ => []
  | .node g children => g :: Path.collect (signature.input g) (fun i => witnessList (children i))

theorem ordered_and_distinct : Tree.graft pair first ≠ Tree.graft pair reversed := by
  intro h
  have h' := congrArg witnessList h
  change [Witness.fork, Witness.erase, Witness.tag] =
    [Witness.fork, Witness.tag, Witness.erase] at h'
  cases h'

-- A genuinely nonidentity second stage inserts a binary tree under the unary tag.
def second : Tree.Substitution (Tree.graft pair first) := fun
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => fun i => nomatch i
  | .inr () => fun
      | .inl i => nomatch i
      | .inr () => pair

theorem nontrivial_two_stage_associativity :
    Tree.graft (Tree.graft pair first) second =
    Tree.graft pair (Tree.compose pair first second) := Tree.graft_assoc pair first second

theorem second_stage_computes :
    witnessList (Tree.graft (Tree.graft pair first) second) =
    [Witness.fork, Witness.erase, Witness.tag, Witness.fork] ∧
    (Tree.graft (Tree.graft pair first) second).leaves = [color, color] := ⟨rfl, rfl⟩

example (σ τ : Tree.Substitution empty) : σ = τ := by
  funext i
  exact nomatch i

example : empty.frontier = Quiver.Path.nil := rfl

#print axioms nontrivial_two_stage_associativity
#print axioms independent_replacements
#print axioms second_stage_computes

end Loop

end IndependentAudit
