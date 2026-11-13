module

public import WitnessedDecompositions.Core

/-!
# Checked examples

The first example has four genuinely different interfaces. Two distinct
presentations refine the cuts `1 | 23` and `12 | 3` to the same three-edge path.
The second isolates repeated identical components and nullary witnesses.
These are path-flattening examples, not a graph-cut semantics theorem.
-/

@[expose] public section

namespace WitnessedDecompositions.Examples

open Tree

/-- Supply the two ordered children of a binary input path. -/
def binaryChildren {V : Type} [Quiver V] {S : Signature V}
    {a b c : V} {e : a ⟶ b} {f : b ⟶ c}
    (t : Tree S ⟨a, b, e⟩) (u : Tree S ⟨b, c, f⟩) :
    (i : Path.Slot ((Quiver.Path.nil.cons e).cons f)) →
      Tree S (Path.componentAt ((Quiver.Path.nil.cons e).cons f) i)
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => t
  | .inr () => u

namespace MultiInterface

/-- Four interfaces are used; there are no arrows except the listed components. -/
inductive Edge : Nat → Nat → Type where
  | a : Edge 0 1
  | b : Edge 1 2
  | c : Edge 2 3
  | d : Edge 0 2
  | e : Edge 1 3
  | whole : Edge 0 3

instance : Quiver Nat := ⟨Edge⟩

inductive Witness where
  | split12
  | split23
  | cut1_23
  | cut12_3
  deriving DecidableEq

def signature : Signature Nat where
  Generator := Witness
  source
    | .split12 => 0
    | .split23 => 1
    | .cut1_23 => 0
    | .cut12_3 => 0
  target
    | .split12 => 2
    | .split23 => 3
    | .cut1_23 => 3
    | .cut12_3 => 3
  input
    | .split12 => (Quiver.Path.nil.cons Edge.a).cons Edge.b
    | .split23 => (Quiver.Path.nil.cons Edge.b).cons Edge.c
    | .cut1_23 => (Quiver.Path.nil.cons Edge.a).cons Edge.e
    | .cut12_3 => (Quiver.Path.nil.cons Edge.d).cons Edge.c
  output
    | .split12 => Edge.d
    | .split23 => Edge.e
    | .cut1_23 => Edge.whole
    | .cut12_3 => Edge.whole

def a : Component Nat := ⟨0, 1, Edge.a⟩
def b : Component Nat := ⟨1, 2, Edge.b⟩
def c : Component Nat := ⟨2, 3, Edge.c⟩
def whole : Component Nat := ⟨0, 3, Edge.whole⟩

/-- First cut `1 | 23`, followed by refinement of `23`. -/
def rightGrouped : Tree signature whole :=
  Tree.node (S := signature) Witness.cut1_23 (binaryChildren (.leaf a) (corolla (S := signature) Witness.split23))

/-- First cut `12 | 3`, followed by refinement of `12`. -/
def leftGrouped : Tree signature whole :=
  Tree.node (S := signature) Witness.cut12_3 (binaryChildren (corolla (S := signature) Witness.split12) (.leaf c))

def flat : Quiver.Path (V := Nat) 0 3 :=
  ((Quiver.Path.nil.cons Edge.a).cons Edge.b).cons Edge.c

/-- The retained witnesses and grouping make the presentations distinct. -/
theorem different_presentations : leftGrouped ≠ rightGrouped := by
  intro h
  have hh := congrArg Tree.generators h
  change [Witness.cut12_3, Witness.split12] = [Witness.cut1_23, Witness.split23] at hh
  cases hh

@[simp] theorem left_frontier : frontier leftGrouped = flat := rfl
@[simp] theorem right_frontier : frontier rightGrouped = flat := rfl

/-- Equality of semantic values does not imply equality of presentation trees. -/
theorem equal_flattened_decompositions : frontier leftGrouped = frontier rightGrouped := rfl

theorem evaluation_not_injective :
    ¬ Function.Injective (fun t : Tree signature whole => frontier t) := by
  intro h
  exact different_presentations (h equal_flattened_decompositions)

/-- This is the same equality under the independently defined algebra evaluator. -/
theorem equal_algebra_evaluations :
    Algebra.evaluate Algebra.flattening (fun x => x.edge.toPath) leftGrouped =
      Algebra.evaluate Algebra.flattening (fun x => x.edge.toPath) rightGrouped := rfl

/-- A different target algebra retains the distinction. Nothing in the calculus
forces all interpretations to identify alternative groupings. -/
theorem distinct_presentation_evaluations :
    Algebra.evaluate Algebra.presentation Tree.leaf leftGrouped ≠
      Algebra.evaluate Algebra.presentation Tree.leaf rightGrouped := by
  intro h
  apply different_presentations
  exact (Algebra.evaluate_presentation leftGrouped).symm.trans
    (h.trans (Algebra.evaluate_presentation rightGrouped))

/-- Both are operations with exactly the same typed input and output profile. -/
def leftOperation : Operation (S := signature) whole flat := ⟨leftGrouped, left_frontier⟩
def rightOperation : Operation (S := signature) whole flat := ⟨rightGrouped, right_frontier⟩

theorem distinct_operations : leftOperation ≠ rightOperation := by
  intro h
  exact different_presentations (congrArg Subtype.val h)

/-- Three consecutive components with four distinct interfaces, not a one-color model. -/
theorem ordered_frontier : leaves leftGrouped = [a, b, c] := rfl

/-- The `1 | 23` tree is obtained by an actual simultaneous substitution. -/
def refineRight : Substitution (corolla (S := signature) Witness.cut1_23) :=
  binaryChildren (.leaf a) (corolla (S := signature) Witness.split23)

theorem graft_builds_rightGrouped :
    graft (corolla (S := signature) Witness.cut1_23) refineRight = rightGrouped := rfl

end MultiInterface

namespace RepeatedComponent

/-- This deliberately one-interface *example* tests repeated identical colors;
the generic calculus and the example above do not impose this restriction. -/
instance : Quiver Unit := ⟨fun _ _ => Unit⟩

def component : Component Unit := ⟨(), (), ()⟩

def single : Quiver.Path (V := Unit) () () := Quiver.Path.nil.cons ()
def double : Quiver.Path (V := Unit) () () := single.cons ()

inductive Witness where
  | binary
  | red
  | blue
  | erase
  deriving DecidableEq

def signature : Signature Unit where
  Generator := Witness
  source _ := ()
  target _ := ()
  input
    | .binary => double
    | .red => single
    | .blue => single
    | .erase => Quiver.Path.nil
  output _ := ()

def pair : Tree signature component := corolla (S := signature) Witness.binary
def red : Tree signature component := corolla (S := signature) Witness.red
def blue : Tree signature component := corolla (S := signature) Witness.blue

/-- The two occurrences have exactly the same component type, but receive
*different* replacement trees. -/
def differentReplacements : Substitution pair := binaryChildren red blue

def swappedReplacements : Substitution pair := binaryChildren blue red

theorem independent_occurrences :
    generators (graft pair differentReplacements) = [Witness.binary, Witness.red, Witness.blue] := rfl

theorem order_is_not_quotiented :
    graft pair differentReplacements ≠ graft pair swappedReplacements := by
  intro h
  have hh := congrArg Tree.generators h
  change [Witness.binary, Witness.red, Witness.blue] =
    [Witness.binary, Witness.blue, Witness.red] at hh
  cases hh

/-- A nullary witness is allowed for a loop component and has no leaves. -/
def nullary : Tree signature component := corolla (S := signature) Witness.erase

theorem nullary_frontier : frontier nullary = Quiver.Path.nil := rfl

theorem nullary_has_no_leaves : leaves nullary = [] := rfl

theorem nullary_has_no_occurrences : IsEmpty (Leaf nullary) :=
  ⟨fun ⟨i, _⟩ => nomatch i⟩

theorem nullary_graft (σ : Substitution nullary) : graft nullary σ = nullary := by
  change Tree.node (S := signature) Witness.erase (fun i => graft (Tree.leaf (signature.argument Witness.erase i)) (σ i)) =
    Tree.node (S := signature) Witness.erase (fun i => Tree.leaf (signature.argument Witness.erase i))
  congr 1
  funext i
  exact nomatch i

/-- Nullaries may also be inserted independently at repeated occurrences. -/
def eraseFirst : Substitution pair := binaryChildren nullary blue

theorem nullary_insertion : generators (graft pair eraseFirst) =
    [Witness.binary, Witness.erase, Witness.blue] ∧
    leaves (graft pair eraseFirst) = [component] := ⟨rfl, rfl⟩

/-- The generic associativity theorem covers a genuine two-stage replacement. -/
def secondStage : Substitution (graft pair differentReplacements) :=
  fun i => match i with
  | .inl (.inl impossible) => nomatch impossible
  | .inl (.inr ()) => fun j => match j with
      | .inl impossible => nomatch impossible
      | .inr () => nullary
  | .inr () => fun j => match j with
      | .inl impossible => nomatch impossible
      | .inr () => red

theorem concrete_associativity :
    graft (graft pair differentReplacements) secondStage =
      graft pair (compose pair differentReplacements secondStage) :=
  graft_assoc pair differentReplacements secondStage

end RepeatedComponent

end WitnessedDecompositions.Examples
