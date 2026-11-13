module
public import research.workstream_C2.lean.RelationInterface
@[expose] public section
open WitnessedDecompositions
open WitnessedDecompositions.RelationInterface
namespace C2IndependentReview

def oldX (_ : Unit) := Unit
def newX (_ : Unit) := Bool
def a : Interface Unit oldX := ⟨()⟩
def constant (_ : Unit) (_ : Bool) : Unit := ()

theorem constant_onto : Function.Surjective (constant ()) := by
  intro y
  cases y
  exact ⟨false, rfl⟩

theorem constant_not_injective : ¬Function.Injective (constant ()) := by
  intro h
  have absurd : (false : Bool) = true := h (show constant () false = constant () true from rfl)
  cases absurd

/-- An onto map does not preserve exactness of the actual nullary operation. -/
theorem onto_nullary_not_exact :
    evaluate ((restrictionQuiver constant).mapPath (Quiver.Path.nil : Quiver.Path a a)) ≠
      (restrictionQuiver constant).map (evaluate (Quiver.Path.nil : Quiver.Path a a)) := by
  intro h
  exact constant_not_injective ((restriction_nullary_eq_iff constant a).mp h)

/-- Nevertheless the original exact nullary restricts as an actual public containment operation. -/
def oldNullary : ContainmentOp (⟨a,a,diagonal a⟩ : Component (Interface Unit oldX)) :=
  ⟨Quiver.Path.nil, fun _ _ h => h⟩
def newNullary := restrictContainment constant oldNullary

theorem newNullary_profile : newNullary.val = Quiver.Path.nil := rfl

def b : Interface Unit newX := ⟨()⟩
def top : Rel b b := fun _ _ => True
def diagonalCell : ContainmentOp (⟨b,b,top⟩ : Component (Interface Unit newX)) :=
  ⟨(diagonal b).toPath, fun _ _ _ => True.intro⟩

/-- The nonexact unary containment operation cannot be represented in its exact fibre. -/
theorem diagonalCell_no_exact :
    IsEmpty ((exactCalc (X := newX)).Operation
      (⟨b,b,top⟩ : Component (Interface Unit newX)) (diagonal b).toPath) := by
  constructor
  intro z
  have eq := z.val.property
  have hp : z.val.val = (diagonal b).toPath := z.property
  change evaluate z.val.val = top at eq
  rw [hp] at eq
  exact (diagonal_containment_nonexact b false true (by intro h; cases h)).2 eq

/-- A fixed output has different total operations when its full profiles differ. -/
theorem profile_retained :
    diagonalCell ≠ (containmentCalc (X := newX)).identity
      (⟨b,b,top⟩ : Component (Interface Unit newX)) := by
  intro h
  have hp := congrArg Subtype.val h
  have he := congrArg evaluate hp
  change evaluate (diagonal b).toPath = evaluate top.toPath at he
  rw [evaluate_edge,evaluate_edge] at he
  exact (diagonal_containment_nonexact b false true (by intro h; cases h)).2
    ((evaluate_edge (diagonal b)).trans he)

#check containmentCalc
#check exactCalc
#check exactInclusion
#check containmentFiberEquiv
#check exactFiberEquiv
#check presentationExtension_unique
#print axioms onto_nullary_not_exact
#print axioms newNullary
#print axioms diagonalCell_no_exact
#print axioms profile_retained
end C2IndependentReview
