import D1FiniteTypedAction
import research.workstream_C2.lean.RelationInterface
import WitnessedDecompositions.RefinementFunctoriality

/-! Genuine finite Signature/Assignment instantiation in the frozen original API.
This module does not claim a generic changed-quiver Calc.Hom exists in that API.
-/
set_option backward.isDefEq.respectTransparency false
namespace D1OriginalAPIBridge
open D1FiniteTypedAction

abbrev V := WitnessedDecompositions.RelationInterface.Interface Interface (fun _ => Point)
def vertex (a : Interface) : V := ⟨a⟩

inductive Generator where
  | binary (a b c : Interface) (R : Rel a b) (S : Rel b c) (decoration : Bool)
  | unit (a : Interface)

def signature : WitnessedDecompositions.Signature V where
  Generator := Generator
  source
    | .binary a _ _ _ _ _ => vertex a
    | .unit a => vertex a
  target
    | .binary _ _ c _ _ _ => vertex c
    | .unit a => vertex a
  input
    | .binary a b _ R S _ =>
      ((Quiver.Path.nil : Quiver.Path (vertex a) (vertex a)).cons (c := vertex b) R).cons S
    | .unit _ => Quiver.Path.nil
  output
    | .binary _ _ _ R S _ => comp R S
    | .unit a => diagonal a

/-- Each primitive is actually admissible in the existing exact relational Calc. -/
theorem primitive_exact (g : Generator) :
    WitnessedDecompositions.RelationInterface.evaluate (signature.input g) = signature.output g := by
  cases g with
  | binary a b c R S k =>
    change WitnessedDecompositions.RelationInterface.comp (WitnessedDecompositions.RelationInterface.comp (WitnessedDecompositions.RelationInterface.diagonal (vertex a)) R) S = comp R S
    rw [WitnessedDecompositions.RelationInterface.comp_diagonal_left]
    rfl
  | unit a => rfl

def exactAssignment : signature.Assignment WitnessedDecompositions.RelationInterface.exactCalc :=
  fun g => ⟨⟨signature.input g, primitive_exact g⟩, rfl⟩

def freeExtension : WitnessedDecompositions.Calc.Hom (WitnessedDecompositions.Tree.freeCalc signature) WitnessedDecompositions.RelationInterface.exactCalc :=
  WitnessedDecompositions.Tree.extend WitnessedDecompositions.RelationInterface.exactCalc exactAssignment

/-- Canonical finite carrier permutations act on primitive witnesses, not just names. -/
def transportGenerator (p : Action) : Generator → Generator
  | .binary a b c R S k => .binary a b c (transportRel p R) (transportRel p S) k
  | .unit a => .unit a

def transportPath (p : Action) {a : V} : {b : V} → Quiver.Path a b → Quiver.Path a b
  | _, .nil => .nil
  | _, @Quiver.Path.cons _ _ _ b c q R =>
      (transportPath p q).cons (transportRel p (a := b.label) (b := c.label) R)

theorem transportGenerator_identity (g : Generator) :
    transportGenerator identityAction g = g := by cases g <;> rfl

theorem transportGenerator_composite (p q : Action) (g : Generator) :
    transportGenerator q (transportGenerator p g) = transportGenerator (thenAction p q) g := by
  cases g <;> rfl

/-- HEq records only the definitional endpoint casts in the dependent Signature API. -/
theorem primitive_profile_action (p : Action) (g : Generator) :
    HEq (signature.input (transportGenerator p g)) (transportPath p (signature.input g)) := by
  cases g <;> rfl

theorem transportPath_identity {a b : V} (q : Quiver.Path a b) :
    transportPath identityAction q = q := by
  induction q with
  | nil => rfl
  | cons q R ih => simp only [transportPath, transportRel_identity, ih]

theorem transportPath_composite (p q : Action) {a b : V} (r : Quiver.Path a b) :
    transportPath q (transportPath p r) = transportPath (thenAction p q) r := by
  induction r with
  | nil => rfl
  | cons r R ih => simp only [transportPath, transportRel_composite, ih]

theorem transported_primitive_exact (p : Action) (g : Generator) :
    WitnessedDecompositions.RelationInterface.evaluate (signature.input (transportGenerator p g)) =
      signature.output (transportGenerator p g) := primitive_exact _

theorem primitive_output_action (p : Action) (g : Generator) :
    signature.output (transportGenerator p g) =
      transportRel p (a := (signature.source g).label) (b := (signature.target g).label)
        (signature.output g) := by
  cases g with
  | binary a b c R S k => exact (transportRel_comp p R S).symm
  | unit a => exact (transportRel_diagonal p a).symm

theorem path_evaluation_action (p : Action) {a b : V} (q : Quiver.Path a b) :
    WitnessedDecompositions.RelationInterface.evaluate (transportPath p q) =
      transportRel p (a := a.label) (b := b.label) (WitnessedDecompositions.RelationInterface.evaluate q) := by
  induction q with
  | nil => exact (transportRel_diagonal p a.label).symm
  | @cons b c q R ih =>
    change WitnessedDecompositions.RelationInterface.comp (WitnessedDecompositions.RelationInterface.evaluate (transportPath p q))
      (transportRel p (a := b.label) (b := c.label) R) = _
    rw [ih]
    exact (transportRel_comp p (WitnessedDecompositions.RelationInterface.evaluate q) R).symm

/-- The source calculus really retains parallel decorated generator witnesses. -/
theorem distinct_binary_generators (a b c : Interface) (R : Rel a b) (S : Rel b c) :
    Generator.binary a b c R S false ≠ Generator.binary a b c R S true := by
  intro h
  cases h

#print axioms primitive_profile_action
#print axioms transportGenerator_composite
#print axioms transportPath_composite
#print axioms primitive_exact
#print axioms primitive_output_action
#print axioms path_evaluation_action
#print axioms transported_primitive_exact
#print axioms freeExtension
#print axioms distinct_binary_generators
end D1OriginalAPIBridge
