import E1RelationEquipment

/-! Finite typed witnesses in the actual original quiver/API. Each interface has
Bool carrier, but the three interface tags remain distinct. Scalars are naturals;
the example does not pretend that a bounded scalar list is substitution-closed. -/
namespace E1FiniteExamples
open WitnessedDecompositions E1RelationEquipment
inductive Tag where | a | b | c deriving DecidableEq
abbrev X (_ : Tag) := Bool
abbrev Vertex := RelationInterface.Interface Tag X
def a : Vertex := ⟨.a⟩
def b : Vertex := ⟨.b⟩
def c : Vertex := ⟨.c⟩
def same {u v : Vertex} : u ⟶ v := fun x y => x = y
def total {u v : Vertex} : u ⟶ v := fun _ _ => True

def twice : Quiver.Path a c := ((Quiver.Path.nil : Quiver.Path a a).cons (same (v := b))).cons same

theorem multiple_components : (same : a ⟶ c) ≠ total := by
  intro h
  have hh := congrFun (congrFun h false) true
  have : (false : Bool) = true := hh.mpr trivial
  contradiction

theorem nonidentity_vertical : (Bool.not : Bool → Bool) ≠ id := by
  intro h
  have := congrFun h false
  contradiction

def nonglobular (n : Nat) : Cell twice (total : b ⟶ a) Bool.not (fun _ => false) :=
  ⟨n, fun _ _ _ => trivial⟩

theorem parallel_cells : nonglobular 2 ≠ nonglobular 3 := by
  intro h
  have := congrArg Cell.weight h
  contradiction

/-- The lift along genuinely nonidentity sides retains a nonzero witness. -/
def nonglobularLift : Cell twice (restrict (total : b ⟶ a) Bool.not (fun _ => false)) id id :=
  restrictionEquiv twice total Bool.not (fun _ => false) id id (nonglobular 2)

theorem nonidentity_factorization :
    restrictionCompose twice total Bool.not (fun _ => false) id id nonglobularLift = nonglobular 2 :=
  restriction_factorization twice total Bool.not (fun _ => false) id id (nonglobular 2)

theorem nonidentity_lift_weight : nonglobularLift.weight = 2 := rfl

/-- Both vertical changes are nonidentity and order matters. -/
theorem two_vertical_changes :
    restrict (a := a) (b := c) (restrict (a := a) (b := c) (same : a ⟶ c) Bool.not id) (fun _ => false) Bool.not =
      restrict (a := a) (b := c) (same : a ⟶ c) (Bool.not ∘ fun _ => false) (id ∘ Bool.not) := rfl

theorem reversed_changes_wrong :
    ¬ (restrict (a := a) (b := c) (restrict (a := a) (b := c) (same : a ⟶ c) Bool.not id) (fun _ => false) Bool.not false false ↔
      restrict (a := a) (b := c) (same : a ⟶ c) ((fun _ => false) ∘ Bool.not) Bool.not false false) := by
  change ¬ ((true : Bool) = true ↔ (false : Bool) = true)
  decide

def looseCore : CoreOp ⟨a, c, total⟩ := ⟨twice, 2, fun _ _ _ => trivial⟩

theorem legitimate_nonuniversal : ¬ ContextualOpcartesian looseCore.cell := by
  intro h
  have hh := (contextual_marked looseCore h).2
  contradiction

theorem twice_evaluate : RelationInterface.evaluate twice = (same : a ⟶ c) := by
  funext x y
  simp [twice, same, RelationInterface.evaluate, RelationInterface.comp, RelationInterface.diagonal]

def exactBinary : (RelationInterface.exactCalc (X := X)).Op ⟨a, c, same⟩ := ⟨twice, twice_evaluate⟩

theorem marked_binary_universal : ContextualOpcartesian (exactLift.map exactBinary).cell :=
  marked_contextual _ (exactLift_marked _)

def swap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv x := Bool.not_not x
  right_inv x := Bool.not_not x

def swapAction : Action X := fun _ => swap

theorem marked_change_preserved : Marked (actCore swapAction (exactLift.map exactBinary)) :=
  actCore_marked _ _ (exactLift_marked _)

theorem two_marked_changes :
    actCore swapAction (actCore swapAction (exactLift.map exactBinary)) =
      actCore (thenAction swapAction swapAction) (exactLift.map exactBinary) :=
  actCore_composite _ _ _

theorem nullary_distinction : nullaryPrimitive b 1 ≠ unitCell b := primitive_not_unit b

theorem nullary_primitive_nonuniversal : ¬ ContextualOpcartesian (nullaryPrimitive b 1) :=
  primitive_not_contextual b

theorem nullary_unit_universal : ContextualOpcartesian (unitCell b) := unit_is_contextual b

/-- A nonempty prefix AND suffix surrounding the nullary universal unit. -/
theorem middle_unit_context :
    Function.Bijective (contextSubstitute (same (u := a) (v := b)).toPath
      (same (u := b) (v := c)).toPath (unitCell b) (total : a ⟶ c) id id) :=
  unit_is_contextual b _ _ _ _ _

/-- Refined operations are represented through the actual original Signature API. -/
theorem original_signature_image :
    ∃ t : Tree equipmentSignature ⟨a, c, total⟩, freeCoreMap.map t = looseCore :=
  freeCoreMap_surjective _ _

#print axioms multiple_components
#print axioms nonidentity_vertical
#print axioms parallel_cells
#print axioms nonidentity_factorization
#print axioms two_vertical_changes
#print axioms reversed_changes_wrong
#print axioms legitimate_nonuniversal
#print axioms marked_binary_universal
#print axioms marked_change_preserved
#print axioms two_marked_changes
#print axioms nullary_distinction
#print axioms nullary_primitive_nonuniversal
#print axioms nullary_unit_universal
#print axioms middle_unit_context
#print axioms original_signature_image
end E1FiniteExamples
