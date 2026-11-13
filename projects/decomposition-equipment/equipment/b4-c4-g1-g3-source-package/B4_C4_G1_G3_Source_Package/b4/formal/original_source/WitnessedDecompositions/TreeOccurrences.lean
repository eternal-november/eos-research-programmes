module

public import WitnessedDecompositions.Collections
public import WitnessedDecompositions.PathOccurrences

/-! Ordered, component-preserving correspondence between profile positions and tree leaves. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u v w z

namespace WitnessedDecompositions.Tree

variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Every frontier position is exactly one leaf occurrence, including repeated colors. -/
def frontierLeafEquiv : {c : Component V} → (t : Tree S c) → Path.Slot (frontier t) ≃ Leaf t
  | _, .leaf _ =>
    { toFun := fun i => match i with | .inl j => nomatch j | .inr u => u
      invFun := Sum.inr
      left_inv := by rintro (i | ⟨⟩); exact nomatch i; rfl
      right_inv := fun _ => rfl }
  | _, .node g children =>
      (Path.slotExpand (S.input g) (fun i => frontier (children i))).trans
        { toFun := fun x => ⟨x.1, frontierLeafEquiv (children x.1) x.2⟩
          invFun := fun x => ⟨x.1, (frontierLeafEquiv (children x.1)).symm x.2⟩
          left_inv := by
            rintro ⟨i, j⟩
            exact congrArg (Sigma.mk i) ((frontierLeafEquiv (children i)).left_inv j)
          right_inv := by
            rintro ⟨i, j⟩
            exact congrArg (Sigma.mk i) ((frontierLeafEquiv (children i)).right_inv j) }

/-- The occurrence correspondence preserves full components, not just colors' names. -/
theorem frontierLeafEquiv_component {c : Component V} (t : Tree S c)
    (i : Path.Slot (frontier t)) :
    Path.componentAt (frontier t) i = leafComponent t (frontierLeafEquiv t i) := by
  induction t with
  | leaf c => cases i with
    | inl i => exact nomatch i
    | inr i => cases i; rfl
  | node g children ih =>
    exact (Path.componentAt_slotExpand (S.input g) (fun i => frontier (children i)) i).trans
      (ih (Path.slotExpand (S.input g) (fun i => frontier (children i)) i).1
        (Path.slotExpand (S.input g) (fun i => frontier (children i)) i).2)

/-- The inverse occurrence correspondence also preserves the entire component. -/
theorem frontierLeafEquiv_symm_component {c : Component V} (t : Tree S c) (l : Leaf t) :
    Path.componentAt (frontier t) ((frontierLeafEquiv t).symm l) = leafComponent t l := by
  simpa only [Equiv.apply_symm_apply] using
    frontierLeafEquiv_component t ((frontierLeafEquiv t).symm l)

theorem cast_congrArg (F : Component V → Sort z) {c d : Component V}
    (h : c = d) (x : F c) :
    cast (congrArg F h) x = Path.occurrenceTransport F h x := by
  cases h
  rfl

theorem occurrenceTransport_heq (F : Component V → Sort z) {c d : Component V}
    (h : c = d) (x : F c) : HEq (Path.occurrenceTransport F h x) x := by
  cases h
  rfl

theorem dependent_apply_heq {α : Sort _} {F : α → Sort _} (f : ∀ a, F a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

/-- Arbitrary component-indexed values can be transported in both directions. -/
def leafFamilyEquiv (F : Component V → Sort z) {c : Component V} (t : Tree S c) :
    (∀ i : Path.Slot (frontier t), F (Path.componentAt (frontier t) i)) ≃
      (∀ l : Leaf t, F (leafComponent t l)) where
  toFun f l := Path.occurrenceTransport F (frontierLeafEquiv_symm_component t l)
    (f ((frontierLeafEquiv t).symm l))
  invFun f i := Path.occurrenceTransport F (frontierLeafEquiv_component t i).symm
    (f (frontierLeafEquiv t i))
  left_inv f := by
    funext i
    apply eq_of_heq
    exact (occurrenceTransport_heq F _ _).trans ((occurrenceTransport_heq F _ _).trans
      (dependent_apply_heq f ((frontierLeafEquiv t).symm_apply_apply i)))
  right_inv f := by
    funext l
    apply eq_of_heq
    exact (occurrenceTransport_heq F _ _).trans ((occurrenceTransport_heq F _ _).trans
      (dependent_apply_heq f ((frontierLeafEquiv t).apply_symm_apply l)))

@[simp] theorem leafFamilyEquiv_apply (F : Component V → Sort z)
    {c : Component V} (t : Tree S c)
    (f : ∀ i : Path.Slot (frontier t), F (Path.componentAt (frontier t) i)) (l : Leaf t) :
    leafFamilyEquiv F t f l =
      Path.occurrenceTransport F (frontierLeafEquiv_symm_component t l)
        (f ((frontierLeafEquiv t).symm l)) := rfl

/-- The seed's structural products are equivalent to the prescribed profile-slot family. -/
def profileSubstitutionEquiv {c : Component V} (t : Tree S c) :
    (collection S).Family (frontier t) ≃ Substitution t :=
  (leafFamilyEquiv (Tree S) t).trans (substitutionEquiv t).symm

/-- Grafting given a family indexed by the actual ordered frontier profile. -/
def profileGraft : {c : Component V} → (t : Tree S c) →
    (collection S).Family (frontier t) → Tree S c
  | _, .leaf _, f => f (.inr ())
  | _, .node g children, f => .node g (fun i =>
      profileGraft (children i)
        (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i))

/-- A proof of frontier equality gives a canonical occurrence equivalence for a fixed fibre. -/
def operationLeafEquiv {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) : Path.Slot p ≃ Leaf t.val :=
  (equalityEquiv (congrArg Path.Slot t.property.symm)).trans (frontierLeafEquiv t.val)

/-- A fixed operation fibre uses positions of p, not a presentation-specific product. -/
def operationSubstitutionEquiv {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) : (collection S).Family p ≃ Substitution t.val :=
  (equalityEquiv (congrArg ((collection S).Family) t.property.symm)).trans
    (profileSubstitutionEquiv t.val)

/-- Every identity substitution reads as the corresponding identity leaf. -/
@[simp] theorem atLeaf_identity {c : Component V} (t : Tree S c) (l : Leaf t) :
    atLeaf t (identity t) l = .leaf (leafComponent t l) := by
  induction t with
  | leaf c => cases l; rfl
  | node g children ih => exact ih l.1 l.2

@[simp] theorem occurrenceTransport_leaf {c d : Component V} (h : c = d) :
    Path.occurrenceTransport (Tree S) h (.leaf c) = .leaf d := by
  cases h
  rfl

/-- Profile-indexed identity substitution is exactly the seed's structural identity. -/
@[simp] theorem profileSubstitutionEquiv_identity {c : Component V} (t : Tree S c) :
    profileSubstitutionEquiv t (fun i => .leaf (Path.componentAt (frontier t) i)) =
      identity t := by
  apply (substitutionEquiv t).injective
  funext l
  change atLeaf t (fromLeaves t (leafFamilyEquiv (Tree S) t
    (fun i => .leaf (Path.componentAt (frontier t) i)))) l = atLeaf t (identity t) l
  rw [atLeaf_fromLeaves, atLeaf_identity]
  rw [leafFamilyEquiv_apply, occurrenceTransport_leaf]

/-- A node's profile family splits into the independently ordered child families. -/
theorem leafFamilyEquiv_node (F : Component V → Sort z)
    (g : S.Generator) (children : ∀ i, Tree S (S.argument g i))
    (f : ∀ i : Path.Slot (frontier (.node g children)),
      F (Path.componentAt (frontier (.node g children)) i))
    (i : Path.Slot (S.input g)) (l : Leaf (children i)) :
    leafFamilyEquiv F (.node g children) f ⟨i, l⟩ =
      leafFamilyEquiv F (children i)
        (Path.expandFamily F (S.input g) (fun i => frontier (children i)) f i) l := by
  rw [leafFamilyEquiv_apply, leafFamilyEquiv_apply]
  unfold Path.expandFamily
  rw [Path.occurrenceTransport_trans]
  rfl

/-- Recursive decomposition of a genuine profile-indexed substitution. -/
theorem profileSubstitutionEquiv_node
    (g : S.Generator) (children : ∀ i, Tree S (S.argument g i))
    (f : (collection S).Family (frontier (.node g children))) :
    profileSubstitutionEquiv (.node g children) f = fun i =>
      profileSubstitutionEquiv (children i)
        (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i) := by
  funext i
  apply (substitutionEquiv (children i)).injective
  funext l
  change atLeaf (children i)
    (fromLeaves (children i) (fun l => leafFamilyEquiv (Tree S) (.node g children) f ⟨i, l⟩)) l =
    atLeaf (children i) (fromLeaves (children i)
      (leafFamilyEquiv (Tree S) (children i)
        (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i))) l
  rw [atLeaf_fromLeaves, atLeaf_fromLeaves]
  exact leafFamilyEquiv_node _ _ _ _ _ _

@[simp] theorem profileGraft_node
    (g : S.Generator) (children : ∀ i, Tree S (S.argument g i))
    (f : (collection S).Family (frontier (.node g children))) :
    profileGraft (.node g children) f = .node g (fun i =>
      profileGraft (children i)
        (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i)) := rfl

/-- The profile recursion is exactly the seed graft, not a new syntax or quotient. -/
theorem profileGraft_eq_graft {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t)) :
    profileGraft t f = graft t (profileSubstitutionEquiv t f) := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
    rw [profileSubstitutionEquiv_node]
    change Tree.node g _ = Tree.node g _
    congr 1
    funext i
    exact ih i _

/-- Right unit for the actual profile-slot operation, before choosing a prescribed fibre. -/
@[simp] theorem profileGraft_identity {c : Component V} (t : Tree S c) :
    profileGraft t (fun i => .leaf (Path.componentAt (frontier t) i)) = t := by
  rw [profileGraft_eq_graft, profileSubstitutionEquiv_identity, graft_identity]

/-- Left unit for the actual profile-slot operation. -/
@[simp] theorem profileGraft_leaf {c : Component V} (t : Tree S c) :
    profileGraft (.leaf c) ((collection S).singletonFamily t) = t := rfl

@[simp] theorem frontier_occurrenceTransport {c d : Component V} (h : c = d) (t : Tree S c) :
    frontier (Path.occurrenceTransport (Tree S) h t) =
      Path.occurrenceTransport (fun c => Quiver.Path c.source c.target) h (frontier t) := by
  cases h
  rfl

/-- The operation profile is prescribed by the supplied slot-indexed family. -/
theorem frontier_profileGraft {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t)) :
    frontier (profileGraft t f) = Path.expand (frontier t) (fun i => frontier (f i)) := by
  induction t with
  | leaf c => exact (Quiver.Path.nil_comp _).symm
  | node g children ih =>
    rw [profileGraft_node]
    change Path.expand (S.input g) (fun i => frontier (profileGraft (children i)
      (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i))) = _
    apply Eq.trans ?_ (Path.expand_assoc (S.input g)
      (fun i => frontier (children i)) (fun i => frontier (f i))).symm
    congr 1
    funext i
    rw [ih]
    congr 1
    funext j
    exact frontier_occurrenceTransport _ _

/-- Substitution into a prescribed fibre, supplied entirely by positions of that profile. -/
def substituteOperation {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i)) :
    Operation (S := S) c (Path.expand p q) :=
  ⟨profileGraft t.val ((collection S).reindex t.property (fun i => (f i).val)), by
    rw [frontier_profileGraft]
    change (collection S).familyProfile
      ((collection S).reindex t.property (fun i => (f i).val)) = _
    rw [Collection.familyProfile_reindex]
    exact congrArg (Path.expand p) (funext (fun i => (f i).property))⟩

/-- The identity operation is a single edge, not an extra primitive unary vertex. -/
def identityOperation (c : Component V) : Operation (S := S) c c.edge.toPath :=
  ⟨.leaf c, rfl⟩

@[simp] theorem reindex_leafFamily {a b : V} {p q : Quiver.Path a b} (h : p = q) :
    (collection S).reindex h (fun i => .leaf (Path.componentAt q i)) =
      (fun i => .leaf (Path.componentAt p i)) := by
  cases h
  rfl

/-- Right unit as equality of operations in the prescribed original fibre. -/
theorem substituteOperation_identity {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) :
    (collection S).transport (Path.expand_edges p)
      (substituteOperation t (fun i => (Path.componentAt p i).edge.toPath)
        (fun i => identityOperation (Path.componentAt p i))) = t := by
  apply Subtype.ext
  change profileGraft t.val
    ((collection S).reindex t.property (fun i => .leaf (Path.componentAt p i))) = t.val
  rw [reindex_leafFamily, profileGraft_identity]

/-- The canonical singleton-profile input family for a supplied operation. -/
def singletonOperationFamily {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) :
    ∀ i : Path.Slot c.edge.toPath,
      Operation (S := S) (Path.componentAt c.edge.toPath i)
        ((collection S).profile ((collection S).singletonFamily t.val i))
  | .inl i => nomatch i
  | .inr () => ⟨t.val, rfl⟩

/-- Left unit as equality in the supplied operation's actual prescribed fibre. -/
theorem identityOperation_substitute {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) :
    (collection S).transport
      (((collection S).singletonFamily_profile t.val).trans t.property)
      (substituteOperation (identityOperation c)
        (fun i => (collection S).profile ((collection S).singletonFamily t.val i))
        (singletonOperationFamily t)) = t := by
  apply Subtype.ext
  rfl

end WitnessedDecompositions.Tree
