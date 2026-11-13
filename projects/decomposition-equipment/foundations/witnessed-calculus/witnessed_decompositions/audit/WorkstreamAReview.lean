import WitnessedDecompositions.Examples
import WitnessedDecompositions.TreeOccurrences
import WitnessedDecompositions.Calculus
import WitnessedDecompositions.FreeExtension
import WitnessedDecompositions.FreeCalculus

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-!
Independent non-author regression tests for workstream A.
These tests initially exercise the seed. They do not establish the missing
arbitrary-signature fibre laws, representation theorem, or universal property.
-/

namespace WorkstreamAReview

open WitnessedDecompositions
open WitnessedDecompositions.Examples (binaryChildren)

inductive Interface where
  | a | b | c
  deriving DecidableEq

inductive Edge : Interface → Interface → Type where
  | x : Edge .a .b
  | r : Edge .b .b
  | y : Edge .b .c
  | tail : Edge .b .c
  | whole : Edge .a .c

instance : Quiver Interface := ⟨Edge⟩

inductive Gen where
  | root | tail | fork | red | blue | erase
  deriving DecidableEq

def S : Signature Interface where
  Generator := Gen
  source
    | .root => .a
    | _ => .b
  target
    | .root | .tail => .c
    | _ => .b
  input
    | .root => (Quiver.Path.nil.cons Edge.x).cons Edge.tail
    | .tail => (Quiver.Path.nil.cons Edge.r).cons Edge.y
    | .fork => (Quiver.Path.nil.cons Edge.r).cons Edge.r
    | .red | .blue => Quiver.Path.nil.cons Edge.r
    | .erase => Quiver.Path.nil
  output
    | .root => Edge.whole
    | .tail => Edge.tail
    | .fork | .red | .blue | .erase => Edge.r

def x : Component Interface := ⟨.a, .b, Edge.x⟩
def r : Component Interface := ⟨.b, .b, Edge.r⟩
def y : Component Interface := ⟨.b, .c, Edge.y⟩
def w : Component Interface := ⟨.a, .c, Edge.whole⟩

def presentation (first second : Tree S r) : Tree S w :=
  Tree.node (S := S) Gen.root (binaryChildren (.leaf x)
    (Tree.node (S := S) Gen.tail (binaryChildren
      (Tree.node (S := S) Gen.fork (binaryChildren first second)) (.leaf y))))

def base : Tree S w := presentation (.leaf r) (.leaf r)
def red : Tree S r := Tree.corolla (S := S) Gen.red
def blue : Tree S r := Tree.corolla (S := S) Gen.blue
def erased : Tree S r := Tree.corolla (S := S) Gen.erase

def forest (first second : Tree S r) : Tree.Substitution base := fun
  | .inl (.inl i) => nomatch i
  | .inl (.inr ()) => Tree.leaf x
  | .inr () => fun
    | .inl (.inl i) => nomatch i
    | .inl (.inr ()) => fun
      | .inl (.inl i) => nomatch i
      | .inl (.inr ()) => first
      | .inr () => second
    | .inr () => Tree.leaf y

theorem four_ordered_leaves : base.leaves = [x, r, r, y] := rfl

theorem actual_graft (first second : Tree S r) :
    Tree.graft base (forest first second) = presentation first second := by
  change Tree.node (S := S) Gen.root _ = Tree.node (S := S) Gen.root _
  congr 1
  funext i
  rcases i with (i | i)
  · rcases i with (i | i)
    · exact nomatch i
    · cases i; rfl
  · cases i
    change Tree.node (S := S) Gen.tail _ = Tree.node (S := S) Gen.tail _
    congr 1
    funext j
    rcases j with (j | j)
    · rcases j with (j | j)
      · exact nomatch j
      · cases j
        change Tree.node (S := S) Gen.fork _ = Tree.node (S := S) Gen.fork _
        congr 1
        funext k
        rcases k with (k | k)
        · rcases k with (k | k)
          · exact nomatch k
          · cases k; rfl
        · cases k; rfl
    · cases j; rfl

theorem repeated_occurrences_distinguished :
    Tree.graft base (forest red blue) ≠ Tree.graft base (forest blue red) := by
  intro h
  have hh := congrArg Tree.generators h
  change [Gen.root, Gen.tail, Gen.fork, Gen.red, Gen.blue] =
    [Gen.root, Gen.tail, Gen.fork, Gen.blue, Gen.red] at hh
  cases hh

theorem same_profile_does_not_identify_trees :
    (Tree.graft base (forest red blue)).frontier =
      (Tree.graft base (forest blue red)).frontier := rfl

theorem nullary_deletes_loop_not_neighbors :
    (Tree.graft base (forest erased blue)).leaves = [x, r, y] := rfl

theorem nullary_at_different_occurrence_still_distinct :
    Tree.graft base (forest erased blue) ≠ Tree.graft base (forest blue erased) := by
  intro h
  have hh := congrArg Tree.generators h
  change [Gen.root, Gen.tail, Gen.fork, Gen.erase, Gen.blue] =
    [Gen.root, Gen.tail, Gen.fork, Gen.blue, Gen.erase] at hh
  cases hh

theorem primitive_unary_is_not_identity : red ≠ Tree.leaf r := by
  intro h
  have hh := congrArg Tree.generators h
  cases hh

theorem nullary_is_not_identity : erased ≠ Tree.leaf r := by
  intro h
  have hh := congrArg Tree.generators h
  cases hh

-- Nullary nonloop and noncomposable/reversed paths are rejected by typing.
example : Quiver.Path Interface.a Interface.c := by
  fail_if_success exact Quiver.Path.nil
  fail_if_success exact (Quiver.Path.nil.cons Edge.y).cons Edge.x
  fail_if_success exact (Quiver.Path.nil.cons Edge.x).cons Edge.x
  exact (Quiver.Path.nil.cons Edge.x).cons Edge.y

-- A similarly shaped but wrong-output replacement cannot be used.
example : Tree S r := by
  fail_if_success exact Tree.leaf (S := S) x
  exact red

#print axioms repeated_occurrences_distinguished
#print axioms same_profile_does_not_identify_trees
#print axioms nullary_deletes_loop_not_neighbors
#print axioms nullary_at_different_occurrence_still_distinct
#print axioms primitive_unary_is_not_identity
#print axioms nullary_is_not_identity

/-- Advertised input profile is specified independently of the presentation. -/
def advertisedProfile : Quiver.Path Interface.a Interface.c :=
  (((Quiver.Path.nil.cons Edge.x).cons Edge.r).cons Edge.r).cons Edge.y

def advertisedOperation : Tree.Operation (S := S) w advertisedProfile := ⟨base, rfl⟩

/-- This family is indexed by the four advertised path positions, not Tree.Leaf. -/
def advertisedFamily (first second : Tree S r) :
    (Tree.collection S).Family advertisedProfile := fun
  | .inl (.inl (.inl (.inl i))) => nomatch i
  | .inl (.inl (.inl (.inr ()))) => .leaf x
  | .inl (.inl (.inr ())) => first
  | .inl (.inr ()) => second
  | .inr () => .leaf y

def prescribedInputGraft (first second : Tree S r) : Tree S w :=
  Tree.graft advertisedOperation.val
    (Tree.operationSubstitutionEquiv advertisedOperation (advertisedFamily first second))

theorem prescribed_positions_read_in_order :
    (prescribedInputGraft red blue).generators =
      [Gen.root, Gen.tail, Gen.fork, Gen.red, Gen.blue] := rfl

theorem prescribed_nullary_reads_correct_slot :
    (prescribedInputGraft erased blue).leaves = [x, r, y] := rfl

theorem prescribed_repeated_positions_stay_distinct :
    prescribedInputGraft erased blue ≠ prescribedInputGraft blue erased := by
  intro h
  have hh := congrArg Tree.generators h
  change [Gen.root, Gen.tail, Gen.fork, Gen.erase, Gen.blue] =
    [Gen.root, Gen.tail, Gen.fork, Gen.blue, Gen.erase] at hh
  cases hh

-- This arbitrary-signature equivalence is not merely a counting assertion.
example {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}
    {c : Component V} (t : Tree S c) (l : Tree.Leaf t) :
    Tree.frontierLeafEquiv t ((Tree.frontierLeafEquiv t).symm l) = l :=
  (Tree.frontierLeafEquiv t).apply_symm_apply l

#print axioms Path.slotComp
#print axioms Path.slotExpand
#print axioms Path.expand_assoc
#print axioms Tree.frontierLeafEquiv_component
#print axioms Tree.operationSubstitutionEquiv
#print axioms prescribed_positions_read_in_order
#print axioms prescribed_nullary_reads_correct_slot
#print axioms prescribed_repeated_positions_stay_distinct

/-- The result is now constructed in a specified fibre, not only as an output tree. -/
def fiberResult (first second : Tree S r) :
    Tree.Operation (S := S) w
      (Path.expand advertisedProfile
        (fun i => Tree.frontier (advertisedFamily first second i))) :=
  Tree.substituteOperation advertisedOperation
    (fun i => Tree.frontier (advertisedFamily first second i))
    (fun i => ⟨advertisedFamily first second i, rfl⟩)

def erasedFirstResult : Tree.Operation (S := S) w
    (((Quiver.Path.nil.cons Edge.x).cons Edge.r).cons Edge.y) :=
  fiberResult erased blue

theorem fiber_result_retains_witnesses :
    erasedFirstResult.val.generators =
      [Gen.root, Gen.tail, Gen.fork, Gen.erase, Gen.blue] := rfl

example :
    (Tree.collection S).transport (Path.expand_edges advertisedProfile)
      (Tree.substituteOperation advertisedOperation
        (fun i => (Path.componentAt advertisedProfile i).edge.toPath)
        (fun i => Tree.identityOperation (Path.componentAt advertisedProfile i))) =
      advertisedOperation := Tree.substituteOperation_identity advertisedOperation

#print axioms Tree.frontier_profileGraft
#print axioms Tree.substituteOperation
#print axioms Tree.substituteOperation_identity
#print axioms Tree.identityOperation_substitute
#print axioms fiber_result_retains_witnesses

#print axioms Collection.fiberFamilyEquiv
#print axioms CalcData.composeAt_profile
#print axioms Calc.substitute_assoc
#print axioms Calc.Hom.comp
#print axioms Calc.Hom.onOperation_substitute

#print axioms Path.collect_expand_slots
#print axioms Path.slotExpand_assoc
#print axioms Path.expandFamily_assoc

#print axioms Tree.interpret_profileGraft
#print axioms Tree.interpretFiber_substituteOperation
#print axioms Tree.interpret_unique_of_preserves

/-- The first original repeated slot branches; the second disappears. The
resulting two equal-labelled slots must both belong to the first replacement. -/
def forked : Tree S r := Tree.corolla (S := S) Gen.fork

def firstProfiles := fun i => Tree.frontier (advertisedFamily forked erased i)
def firstOperations (i : Path.Slot advertisedProfile) :
    Tree.Operation (S := S) (Path.componentAt advertisedProfile i) (firstProfiles i) :=
  ⟨advertisedFamily forked erased i, rfl⟩

def secondFamily : (Tree.collection S).Family
    (Path.expand advertisedProfile firstProfiles) := advertisedFamily red blue
def secondProfiles := fun i => Tree.frontier (secondFamily i)
def secondOperations (i : Path.Slot (Path.expand advertisedProfile firstProfiles)) :
    Tree.Operation (S := S)
      (Path.componentAt (Path.expand advertisedProfile firstProfiles) i) (secondProfiles i) :=
  ⟨secondFamily i, rfl⟩

def nestedResult := Tree.substituteOperation
  (Tree.substituteOperation advertisedOperation firstProfiles firstOperations)
  secondProfiles secondOperations

def flattenedResult := Tree.substituteOperation advertisedOperation
  (fun i => Path.expand (firstProfiles i)
    (Path.expandFamily (fun c => Quiver.Path c.source c.target)
      advertisedProfile firstProfiles secondProfiles i))
  (fun i => Tree.substituteOperation (firstOperations i)
    (Path.expandFamily (fun c => Quiver.Path c.source c.target)
      advertisedProfile firstProfiles secondProfiles i)
    ((Tree.freeCalc S).expandOperations advertisedProfile firstProfiles
      secondProfiles secondOperations i))

theorem actual_nested_fibre_associativity :
    (Tree.collection S).transport
      (Path.expand_assoc advertisedProfile firstProfiles secondProfiles)
      nestedResult = flattenedResult :=
  Tree.substituteOperation_assoc advertisedOperation firstProfiles firstOperations
    secondProfiles secondOperations

theorem nested_branch_and_nullary_keep_occurrence_order :
    nestedResult.val.generators =
      [Gen.root, Gen.tail, Gen.fork, Gen.fork, Gen.red, Gen.blue, Gen.erase] := by
  have first_layer_explicit :
      Tree.substituteOperation advertisedOperation firstProfiles firstOperations =
        (⟨presentation forked erased, rfl⟩ : Tree.Operation (S := S) w
          (Path.expand advertisedProfile firstProfiles)) := by
    apply Subtype.ext
    change Tree.node (S := S) Gen.root _ = Tree.node (S := S) Gen.root _
    congr 1
    funext i
    rcases i with (i | i)
    · rcases i with (i | i)
      · exact nomatch i
      · cases i; rfl
    · cases i
      change Tree.node (S := S) Gen.tail _ = Tree.node (S := S) Gen.tail _
      congr 1
      funext j
      rcases j with (j | j)
      · rcases j with (j | j)
        · exact nomatch j
        · cases j
          change Tree.node (S := S) Gen.fork _ = Tree.node (S := S) Gen.fork _
          congr 1
          funext k
          rcases k with (k | k)
          · rcases k with (k | k)
            · exact nomatch k
            · cases k; rfl
          · cases k; rfl
      · cases j; rfl
  unfold nestedResult
  rw [first_layer_explicit]
  rfl

theorem flattened_branch_and_nullary_keep_occurrence_order :
    flattenedResult.val.generators =
      [Gen.root, Gen.tail, Gen.fork, Gen.fork, Gen.red, Gen.blue, Gen.erase] := by
  have h := congrArg (fun t => t.val.generators) actual_nested_fibre_associativity
  exact h.symm.trans nested_branch_and_nullary_keep_occurrence_order

example : Tree.substituteOperation advertisedOperation firstProfiles firstOperations =
    (Tree.freeCalc S).substitute advertisedOperation firstProfiles firstOperations :=
  Tree.substituteOperation_eq_freeCalc_substitute _ _ _

#print axioms Tree.profileGraft_assocAt
#print axioms Tree.profileGraft_assoc
#print axioms Tree.freeCalc
#print axioms Tree.substituteOperation_assoc
#print axioms actual_nested_fibre_associativity
#print axioms flattened_branch_and_nullary_keep_occurrence_order

end WorkstreamAReview
