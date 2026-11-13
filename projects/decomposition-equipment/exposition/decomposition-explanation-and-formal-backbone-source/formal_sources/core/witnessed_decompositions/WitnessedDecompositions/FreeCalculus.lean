module

public import WitnessedDecompositions.TreeOccurrences
public import WitnessedDecompositions.Calculus
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
@[expose] public section

universe u v w z
/-!
Candidate for A1 under CompletionContract v0.1-proposed, SHA256
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
Author-local kernel evidence only; no independent acceptance is asserted.
All base interfaces, edge types and signature generators are arbitrary.
-/

namespace WitnessedDecompositions
namespace Path
variable {V : Type u} [Quiver.{v} V]
/-- Successive path-family transports agree with transport along the composite equality. -/
@[simp] theorem pathFamilyCast_trans (F : Component V → Sort z) {a b : V}
    {p q r : Quiver.Path a b} (e : p = q) (e' : q = r)
    (f : ∀ i : Slot p, F (componentAt p i)) :
    pathFamilyCast F e' (pathFamilyCast F e f) = pathFamilyCast F (e.trans e') f := by
  cases e; cases e'; rfl

/-- Splitting an expanded family commutes with equality of the inserted profiles. -/
theorem expandFamily_pathCast (F : Component V → Sort z) {a b : V} (p : Quiver.Path a b)
    (q q' : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (e : q = q')
    (h : ∀ i : Slot (expand p q'), F (componentAt (expand p q') i)) (i : Slot p) :
    expandFamily F p q (pathFamilyCast F (congrArg (expand p) e).symm h) i =
      pathFamilyCast F (congrFun e i).symm (expandFamily F p q' h i) := by
  cases e; rfl
end Path

namespace Tree
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Tree operations equipped with their occurrence-indexed substitution data. -/
def calcData (S : Signature.{u, v, w} V) : CalcData V where
  toCollection := collection S
  identity := Tree.leaf
  profile_identity _ := rfl
  subst := profileGraft
  profile_subst := frontier_profileGraft

@[simp] theorem reindex_eq_pathFamilyCast {a b : V} {p q : Quiver.Path a b}
    (h : p = q) (f : (collection S).Family q) :
    (collection S).reindex h f = Path.pathFamilyCast (Tree S) h.symm f := by
  cases h
  rfl

/-- Component reindexing commutes with the full profile graft operation. -/
theorem profileGraft_componentCast {c d : Component V} (e : c = d)
    (t : Tree S c) (f : (collection S).Family (frontier t)) :
    Path.occurrenceTransport (Tree S) e (profileGraft t f) =
      profileGraft (Path.occurrenceTransport (Tree S) e t)
        (Path.pathFamilyCast (Tree S) (frontier_occurrenceTransport e t).symm
          (Path.componentPathFamilyCast (Tree S) e (frontier t) f)) := by
  cases e
  rfl

/-- Expansion commutes with the componentwise frontier family. -/
theorem frontier_expandFamily {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p, Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : (collection S).Family (Path.expand p q)) :
    (fun i j => frontier (Path.expandFamily (Tree S) p q f i j)) =
      Path.expandFamily (fun c => Quiver.Path c.source c.target) p q (fun k => frontier (f k)) := by
  funext i j
  exact frontier_occurrenceTransport _ _

/-- Associativity with the second family supplied on the expanded first-layer profile. -/
theorem profileGraft_assocAt {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t))
    (h : (collection S).Family ((collection S).familyProfile f)) :
    profileGraft (profileGraft t f)
      ((collection S).reindex (frontier_profileGraft t f) h) =
    profileGraft t ((calcData S).composeAt f h) := by
  induction t with
  | leaf c =>
    change profileGraft (f (.inr ())) _ = profileGraft (f (.inr ())) _
    congr 1
    funext i
    change (collection S).reindex (frontier_profileGraft (.leaf c) f) h i =
      Path.expandFamily (Tree S) c.edge.toPath (fun i => frontier (f i)) h (.inr ()) i
    rw [Path.expandFamily_edge, reindex_eq_pathFamilyCast]
  | node g children ih =>
    simp only [profileGraft_node]
    congr 1
    funext i
    let p := S.input g
    let q := fun i => frontier (children i)
    let fi := Path.expandFamily (Tree S) p q f
    let r := fun k => frontier (f k)
    let ri := Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r
    have eri : (fun i j => frontier (fi i j)) = ri := frontier_expandFamily p q f
    let qq := fun i => frontier (profileGraft (children i) (fi i))
    let qq' := fun i => Path.expand (q i) (ri i)
    have eqs : qq = qq' := by
      funext i
      exact (frontier_profileGraft (children i) (fi i)).trans
        (congrArg (Path.expand (q i)) (congrFun eri i))
    let hh := Path.pathFamilyCast (Tree S) (Path.expand_assoc p q r) h
    have outerCast : (collection S).reindex (frontier_profileGraft (.node g children) f) h =
        Path.pathFamilyCast (Tree S) (congrArg (Path.expand p) eqs).symm hh := by
      rw [reindex_eq_pathFamilyCast, Path.pathFamilyCast_trans]
    change profileGraft (profileGraft (children i) (fi i))
      (Path.expandFamily (Tree S) p qq _ i) = _
    rw [outerCast, Path.expandFamily_pathCast (Tree S) p qq qq' eqs]
    let hhi := Path.expandFamily (Tree S) p qq' hh i
    let hi : (collection S).Family ((collection S).familyProfile (fi i)) :=
      Path.pathFamilyCast (Tree S) (congrArg (Path.expand (q i)) (congrFun eri i)).symm hhi
    have innerCast : Path.pathFamilyCast (Tree S) (congrFun eqs i).symm hhi =
        (collection S).reindex (frontier_profileGraft (children i) (fi i)) hi := by
      rw [reindex_eq_pathFamilyCast]
      dsimp only [hi]
      rw [Path.pathFamilyCast_trans]
    change profileGraft (profileGraft (children i) (fi i))
      (Path.pathFamilyCast (Tree S) (congrFun eqs i).symm hhi) = _
    rw [innerCast, ih]
    congr 1
    funext j
    change profileGraft (fi i j)
      (Path.expandFamily (Tree S) (q i) (fun j => frontier (fi i j)) hi j) =
      Path.occurrenceTransport (Tree S) (Path.componentAt_slotExpand_symm p q ⟨i, j⟩)
        (profileGraft (f ((Path.slotExpand p q).symm ⟨i, j⟩))
          (Path.expandFamily (Tree S) (Path.expand p q) r h
            ((Path.slotExpand p q).symm ⟨i, j⟩)))
    rw [profileGraft_componentCast]
    congr 1
    dsimp only [hi]
    rw [Path.expandFamily_pathCast (Tree S) (q i)
      (fun j => frontier (fi i j)) (ri i) (congrFun eri i)]
    congr 1
    funext l
    exact Path.expandFamily_assoc (Tree S) p q r h i j l

/-- Literal associativity of retained trees with exactly the generic calculus
composition family and its canonical profile occurrence reindexing. -/
theorem profileGraft_assoc {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t))
    (h : (collection S).Family (frontier (profileGraft t f))) :
    profileGraft (profileGraft t f) h =
      profileGraft t ((calcData S).composeFamily t f h) := by
  have hh := profileGraft_assocAt t f
    ((collection S).reindex (frontier_profileGraft t f).symm h)
  unfold CalcData.composeAt at hh
  unfold CalcData.composeFamily CalcData.innerFamily
  dsimp only [calcData, collection] at *
  simpa only [Collection.reindex_comp, Collection.reindex_refl] using hh

/-- The free path-profile calculus on an arbitrary typed signature, including
nullary loop generators. Its operations are retained trees, not a quotient. -/
def freeCalc (S : Signature.{u, v, w} V) : Calc V where
  toCalcData := calcData S
  subst_identity := profileGraft_identity
  identity_subst := profileGraft_leaf
  subst_assoc := profileGraft_assoc

/-- The already named prescribed-fibre tree substitution is the generic calculus
substitution, so no alternative tree-specific associator is introduced. -/
theorem substituteOperation_eq_freeCalc_substitute {c : Component V}
    {p : Quiver.Path c.source c.target} (t : Operation (S := S) c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i)) :
    substituteOperation t q f = (freeCalc S).substitute t q f := rfl

/-- Associativity in arbitrary, independently prescribed operation fibres.
The named transport is exactly the canonical Path.expand_assoc associator. -/
theorem substituteOperation_assoc {c : Component V}
    {p : Quiver.Path c.source c.target} (t : Operation (S := S) c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i))
    (r : ∀ k : Path.Slot (Path.expand p q),
      Quiver.Path (Path.componentAt (Path.expand p q) k).source
        (Path.componentAt (Path.expand p q) k).target)
    (h : ∀ k : Path.Slot (Path.expand p q),
      Operation (S := S) (Path.componentAt (Path.expand p q) k) (r k)) :
    (collection S).transport (Path.expand_assoc p q r)
      (substituteOperation (substituteOperation t q f) r h) =
      substituteOperation t
        (fun i => Path.expand (q i)
          (Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r i))
        (fun i => substituteOperation (f i)
          (Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r i)
          ((freeCalc S).expandOperations p q r h i)) :=
  Calc.substitute_assoc (freeCalc S) t q f r h

end Tree
end WitnessedDecompositions

