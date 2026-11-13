module

public import WitnessedDecompositions.WeightInvariant
public import WitnessedDecompositions.PresentedCalculus
public import WitnessedDecompositions.Examples

/-! A genuinely mixed-interface equation with a formally separated undeclared parallel pair. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace WitnessedDecompositions.PresentationExamples
open Tree
open Examples (binaryChildren)
namespace Mixed
open Examples.MultiInterface

inductive Gen where
  | cut : Witness → Gen
  | red | blue
  deriving DecidableEq

def S : Signature Nat where
  Generator := Gen
  source
    | .cut g => signature.source g
    | .red | .blue => 0
  target
    | .cut g => signature.target g
    | .red | .blue => 3
  input
    | .cut g => signature.input g
    | .red | .blue => (Quiver.Path.nil.cons Edge.whole)
  output
    | .cut g => signature.output g
    | .red | .blue => Edge.whole

def left : Tree S whole :=
  .node (S := S) (.cut .cut12_3)
    (binaryChildren (corolla (S := S) (.cut .split12)) (.leaf c))

def right : Tree S whole :=
  .node (S := S) (.cut .cut1_23)
    (binaryChildren (.leaf a) (corolla (S := S) (.cut .split23)))

def leftOp : Operation (S := S) whole flat := ⟨left, rfl⟩
def rightOp : Operation (S := S) whole flat := ⟨right, rfl⟩
def red : Tree S whole := corolla (S := S) Gen.red
def blue : Tree S whole := corolla (S := S) Gen.blue

/-- Only the displayed parallel mixed-interface associativity equation is declared. -/
inductive Declared : ∀ (c : Component Nat) (p : Quiver.Path c.source c.target),
    Operation (S := S) c p → Operation (S := S) c p → Prop where
  | associativity : Declared whole flat leftOp rightOp

def equations : Presentation.Equations S := Declared

theorem declared_derivable : Presentation.Derives S equations left right :=
  Presentation.Derives.equation leftOp rightOp Declared.associativity

/-- Red is retained as a witness statistic; all binary grouping generators have weight zero. -/
def redWeight : Gen → Nat
  | .red => 1
  | _ => 0

theorem declaration_preserves_weight :
    ∀ c p (a b : Operation (S := S) c p), equations c p a b →
      weight redWeight a.val = weight redWeight b.val := by
  intro c p a b h
  cases h
  rfl

/-- Parallel primitive witnesses are not silently equated by the declared tree equation. -/
theorem undeclared_not_derivable : ¬ Presentation.Derives S equations red blue := by
  intro h
  have hw := Presentation.derives_weight equations redWeight declaration_preserves_weight h
  change 1 = 0 at hw
  cases hw

theorem undeclared_is_parallel : frontier red = frontier blue := rfl

/-- The declared relation is a genuine relation between different presentations. -/
theorem declared_sides_distinct : left ≠ right := by
  intro h
  have hg := congrArg generators h
  change [Gen.cut .cut12_3, Gen.cut .split12] = [Gen.cut .cut1_23, Gen.cut .split23] at hg
  cases hg

/-- The comparison uses four actual distinct interfaces, not one interface with names. -/
theorem exact_mixed_boundary : leaves left = [a, b, c] := rfl

/-- Applying a witness-retaining unary context preserves the generated equation. -/
theorem declared_in_red_context :
    Presentation.Derives S equations
      (substituteOperation (generatorOperation (S := S) Gen.red)
        (Calc.singletonProfiles (c := whole) flat) ((freeCalc S).singletonOperations leftOp)).val
      (substituteOperation (generatorOperation (S := S) Gen.red)
        (Calc.singletonProfiles (c := whole) flat) ((freeCalc S).singletonOperations rightOp)).val := by
  apply Presentation.Derives.substitute _ _ (Presentation.Derives.refl _) _ _ _
  intro i
  rcases i with i | ⟨⟩
  · exact nomatch i
  · exact declared_derivable

/-- The actual presented quotient identifies the declared grouping equation. -/
theorem declared_quotient_equal :
    (Presentation.projection equations).map left = (Presentation.projection equations).map right :=
  (Presentation.quotient_eq_iff equations left right).2 declared_derivable

/-- The same quotient still separates the undeclared parallel primitive witnesses. -/
theorem undeclared_quotient_distinct :
    (Presentation.projection equations).map red ≠ (Presentation.projection equations).map blue := by
  intro h
  exact undeclared_not_derivable ((Presentation.quotient_eq_iff equations red blue).1 h)

/-- An independently specified semantics retains the full typed profile and red count. -/
noncomputable def statisticModel : Calc Nat := (weightCongruence (S := S) redWeight).quotient

noncomputable def statisticAssignment : S.Assignment statisticModel :=
  Tree.restrict statisticModel (weightCongruence (S := S) redWeight).projection

/-- The statistic semantics satisfies the declaration by an independent additive invariant. -/
theorem statistic_satisfies : Presentation.Satisfies equations statisticModel statisticAssignment := by
  intro c p a b he
  apply Subtype.ext
  change interpret statisticModel statisticAssignment a.val = interpret statisticModel statisticAssignment b.val
  simp only [statisticAssignment, Presentation.interpret_restrict]
  exact ((weightCongruence (S := S) redWeight).quotient_eq_iff a.val b.val).2
    ⟨a.property.trans b.property.symm, declaration_preserves_weight c p a b he⟩

/-- A model of the declared equation separates an undeclared parallel equation. -/
theorem statistic_separates :
    interpret statisticModel statisticAssignment red ≠ interpret statisticModel statisticAssignment blue := by
  simp only [statisticAssignment, Presentation.interpret_restrict]
  intro h
  have hw := ((weightCongruence (S := S) redWeight).quotient_eq_iff red blue).1 h
  have : 1 = 0 := hw.2
  cases this

/- A profile mismatch cannot be smuggled into a declaration. -/
#check_failure (leftOp : Operation (S := S) whole (Quiver.Path.nil.cons Edge.whole))

/- The output mismatch is rejected before equation generation. -/
#check_failure (Tree.leaf a : Tree S whole)

end Mixed

namespace Nullary
open Examples.RepeatedComponent

def noEquations : Presentation.Equations signature := fun _ _ _ _ => False

theorem noEquations_derives_eq {c : Component Unit} {t u : Tree signature c}
    (h : Presentation.Derives signature noEquations t u) : t = u :=
  Presentation.derives_least noEquations
    (ParallelCongruence.kernel (Calc.Hom.id (freeCalc signature)))
    (fun _ _ _ _ h => False.elim h) h

/-- Even an enabled zero-input witness is not converted to the vertex-free identity. -/
theorem nullary_still_not_identity :
    (Presentation.projection noEquations).map nullary ≠
      (Presentation.projection noEquations).map (.leaf component) := by
  intro h
  have ht := noEquations_derives_eq
    ((Presentation.quotient_eq_iff noEquations nullary (.leaf component)).1 h)
  have hg := congrArg generators ht
  change [Witness.erase] = [] at hg
  cases hg

/-- Quotient projection preserves a genuine nullary insertion beside a repeated color. -/
theorem quotient_preserves_nullary_insertion :
    (Presentation.projection noEquations).map
      (profileGraft pair (binaryChildren nullary blue)) =
    (Presentation.quotient noEquations).subst
      ((Presentation.projection noEquations).map pair)
      ((Presentation.quotient noEquations).toCollection.reindex
        ((Presentation.projection noEquations).profile_map pair)
        ((Presentation.projection noEquations).toHom.onFamily (binaryChildren nullary blue))) :=
  (Presentation.projection noEquations).map_subst pair (binaryChildren nullary blue)

end Nullary
end WitnessedDecompositions.PresentationExamples
