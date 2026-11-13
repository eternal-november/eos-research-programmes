module

public import WitnessedDecompositions.TreeOccurrences
public import WitnessedDecompositions.Calculus
public import WitnessedDecompositions.FreeCalculus

/-!
# Extension of primitive assignments into arbitrary target calculi

Leaves are forced to be target identities. No independent atom assignment is
present. These lemmas will be packaged as a strict morphism from the actual
free tree calculus after the separate source associativity proof is installed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z z'

namespace WitnessedDecompositions

namespace Signature

variable {V : Type u} [Quiver.{v} V]

/-- An assignment preserves the entire input profile and output of each primitive. -/
def Assignment (S : Signature.{u, v, w} V) (M : Calc.{u, v, z} V) :=
  ∀ g : S.Generator, M.Operation (S.result g) (S.input g)

end Signature

namespace Tree

variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Recursive interpretation takes values in the actual frontier fibre. -/
def interpretOperation (M : Calc.{u, v, z} V) (a : S.Assignment M) :
    {c : Component V} → (t : Tree S c) → M.Operation c (frontier t)
  | _, .leaf c => M.identityOperation c
  | _, .node g children =>
      M.substitute (a g) (fun i => frontier (children i))
        (fun i => interpretOperation M a (children i))

/-- The underlying operation map, with profile preservation supplied by construction. -/
def interpret (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c : Component V} (t : Tree S c) : M.Op c := (interpretOperation M a t).val

@[simp] theorem interpret_profile (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c : Component V} (t : Tree S c) : M.profile (interpret M a t) = frontier t :=
  (interpretOperation M a t).property

@[simp] theorem interpret_leaf (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (c : Component V) : interpret M a (.leaf c) = M.identity c := rfl

@[simp] theorem interpret_node (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (g : S.Generator) (children : ∀ i, Tree S (S.argument g i)) :
    interpret M a (.node g children) =
      M.subst (a g).val (M.toCollection.reindex (a g).property
        (fun i => interpret M a (children i))) := rfl

/-- The interpretation already defines a strict profile-preserving collection map. -/
def interpretCollectionHom (M : Calc.{u, v, z} V) (a : S.Assignment M) :
    Collection.Hom (collection S) M.toCollection where
  map := interpret M a
  profile_map := interpret_profile M a

/-- Interpretation on any independently prescribed source operation fibre. -/
def interpretFiber (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) : M.Operation c p :=
  (interpretCollectionHom M a).onFiber t

/-- Equality transport forward cancels the matching backwards family reindexing. -/
theorem pathFamilyCast_reindex {x y : V} {p q : Quiver.Path x y} (h : p = q)
    (f : (collection S).Family q) :
    Path.pathFamilyCast (Tree S) h ((collection S).reindex h f) = f := by
  cases h
  rfl

/-- Every constructor node is substitution into its primitive corolla. -/
theorem profileGraft_corolla (g : S.Generator)
    (children : ∀ i, Tree S (S.argument g i)) :
    profileGraft (corolla g) ((collection S).reindex (frontier_corolla g) children) =
      .node g children := by
  change Tree.node g _ = Tree.node g children
  congr 1
  funext i
  change Path.expandFamily (Tree S) (S.input g)
    (fun i => (Path.componentAt (S.input g) i).edge.toPath)
    ((collection S).reindex (frontier_corolla g) children) i (.inr ()) = children i
  exact (Path.expandFamily_edges (Tree S) (S.input g) _ i).trans
    (congrFun (pathFamilyCast_reindex (frontier_corolla g) children) i)

/-- Corollas interpret as precisely the assigned primitive, in its declared fibre. -/
@[simp] theorem interpretOperation_corolla (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (g : S.Generator) :
    M.transport (frontier_corolla g) (interpretOperation M a (corolla g)) = a g :=
  M.substitute_identity (a g)

@[simp] theorem interpret_corolla (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (g : S.Generator) : interpret M a (corolla g) = (a g).val :=
  congrArg Subtype.val (interpretOperation_corolla M a g)

/-- The primitive generator in its actual declared source fibre. -/
def generatorOperation (g : S.Generator) : Operation (S := S) (S.result g) (S.input g) :=
  ⟨corolla g, frontier_corolla g⟩

/-- Corolla decomposition directly in the prescribed tree-operation fibre. -/
theorem substituteOperation_generator (g : S.Generator)
    (children : ∀ i, Tree S (S.argument g i)) :
    substituteOperation (generatorOperation g) (fun i => frontier (children i))
      (fun i => operation (children i)) = operation (.node g children) := by
  apply Subtype.ext
  exact profileGraft_corolla g children

@[simp] theorem interpretFiber_generator (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (g : S.Generator) : interpretFiber M a (generatorOperation g) = a g := by
  apply Subtype.ext
  exact interpret_corolla M a g

/-- Interpretations commute with component-equality transport. -/
@[simp] theorem interpret_occurrenceTransport (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c d : Component V} (h : c = d) (t : Tree S c) :
    interpret M a (Path.occurrenceTransport (Tree S) h t) =
      Path.occurrenceTransport M.Op h (interpret M a t) := by
  cases h
  rfl

/-- Interpret each independently selected branch of an expanded profile. -/
theorem interpret_expandFamily (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {x y : V} (p : Quiver.Path x y)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : (collection S).Family (Path.expand p q))
    (i : Path.Slot p) (j : Path.Slot (q i)) :
    interpret M a (Path.expandFamily (Tree S) p q f i j) =
      Path.expandFamily M.Op p q (fun k => interpret M a (f k)) i j := by
  unfold Path.expandFamily
  exact interpret_occurrenceTransport _ _ _ _

/-- Extension preserves every occurrence-wise substitution into an arbitrary target calculus. -/
theorem interpret_profileGraft (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c : Component V} (t : Tree S c) (f : (collection S).Family (frontier t)) :
    interpret M a (profileGraft t f) = M.subst (interpret M a t)
      (M.toCollection.reindex (interpret_profile M a t) (fun i => interpret M a (f i))) := by
  induction t with
  | leaf c =>
    change interpret M a (f (.inr ())) = M.subst (M.identity c)
      (M.toCollection.reindex (M.profile_identity c) (fun i => interpret M a (f i)))
    have hf : (fun i => interpret M a (f i)) =
        M.toCollection.singletonFamily (interpret M a (f (.inr ()))) := by
      funext i
      rcases i with i | ⟨⟩
      · exact nomatch i
      · rfl
    exact (M.identity_subst (interpret M a (f (.inr ())))).symm.trans
      (congrArg (M.subst (M.identity c))
        (congrArg (M.toCollection.reindex (M.profile_identity c)) hf.symm))
  | node g children ih =>
    have ha := congrArg Subtype.val (M.substitute_assoc (a g)
      (fun i => frontier (children i)) (fun i => interpretOperation M a (children i))
      (fun k => frontier (f k)) (fun k => interpretOperation M a (f k)))
    apply Eq.trans ?_ ha.symm
    change M.subst (a g).val
      (M.toCollection.reindex (a g).property
        (fun i => interpret M a (profileGraft (children i)
          (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i)))) =
      M.subst (a g).val (M.toCollection.reindex (a g).property _)
    congr 1
    apply congrArg (M.toCollection.reindex (a g).property)
    funext i
    rw [ih]
    congr 1
    apply congrArg (M.toCollection.reindex (interpret_profile M a (children i)))
    funext j
    exact interpret_expandFamily M a (S.input g) (fun i => frontier (children i)) f i j

/-- Extension preserves substitution in independently prescribed operation fibres. -/
theorem interpretFiber_substituteOperation (M : Calc.{u, v, z} V) (a : S.Assignment M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i)) :
    interpretFiber M a (substituteOperation t q f) =
      M.substitute (interpretFiber M a t) q (fun i => interpretFiber M a (f i)) := by
  apply Subtype.ext
  rcases t with ⟨t, ht⟩
  cases ht
  exact interpret_profileGraft M a t (fun i => (f i).val)

/-- Structural uniqueness is only an intermediate lemma, not the universal property. -/
theorem interpret_unique (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (F : ∀ {c}, Tree S c → M.Op c)
    (hLeaf : ∀ c, F (.leaf c) = M.identity c)
    (hNode : ∀ g children,
      F (.node g children) = M.subst (a g).val
        (M.toCollection.reindex (a g).property (fun i => F (children i))))
    {c : Component V} (t : Tree S c) : F t = interpret M a t := by
  induction t with
  | leaf c => exact hLeaf c
  | node g children ih =>
    rw [hNode, interpret_node]
    congr 1
    exact congrArg (M.toCollection.reindex (a g).property) (funext ih)

/-- Uniqueness among all profile maps preserving identities, substitution and
primitive images. No recursive node equation is assumed. -/
theorem interpret_unique_of_preserves (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (F : Collection.Hom (collection S) M.toCollection)
    (hLeaf : ∀ c, F.map (.leaf c) = M.identity c)
    (hSubst : ∀ {c : Component V} {p : Quiver.Path c.source c.target}
      (t : Operation (S := S) c p)
      (q : ∀ i : Path.Slot p,
        Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
      (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i)),
      F.onFiber (substituteOperation t q f) =
        M.substitute (c := c) (p := p) (F.onFiber t) q (fun i => F.onFiber (f i)))
    (hGenerator : ∀ g, F.onFiber (generatorOperation g) = a g)
    {c : Component V} (t : Tree S c) : F.map t = interpret M a t := by
  apply interpret_unique M a F.map hLeaf
  intro g children
  have h := hSubst (generatorOperation g) (fun i => frontier (children i))
    (fun i => operation (children i))
  rw [substituteOperation_generator, hGenerator] at h
  exact congrArg Subtype.val h

/-- The genuine extending strict morphism into an arbitrary target calculus. -/
def extend (M : Calc.{u, v, z} V) (a : S.Assignment M) : Calc.Hom (freeCalc S) M where
  toHom := interpretCollectionHom M a
  map_identity _ := rfl
  map_subst := interpret_profileGraft M a

/-- Restrict an arbitrary strict morphism to its primitive generator images. -/
def restrict (M : Calc.{u, v, z} V) (F : Calc.Hom (freeCalc S) M) : S.Assignment M :=
  fun g => F.onOperation (generatorOperation g)

/-- Extension followed by restriction recovers the original assignment. -/
@[simp] theorem restrict_extend (M : Calc.{u, v, z} V) (a : S.Assignment M) :
    restrict M (extend M a) = a := by
  funext g
  exact interpretFiber_generator M a g

/-- Restriction followed by extension recovers EVERY strict morphism. -/
@[simp] theorem extend_restrict (M : Calc.{u, v, z} V) (F : Calc.Hom (freeCalc S) M) :
    extend M (restrict M F) = F := by
  apply Calc.Hom.ext
  intro c t
  symm
  apply interpret_unique_of_preserves M (restrict M F) F.toHom F.map_identity
  · intro c p t q f
    exact F.onOperation_substitute t q f
  · intro g
    rfl

/-- The free universal property: explicit inverse maps, for every target calculus. -/
def homEquiv (M : Calc.{u, v, z} V) : Calc.Hom (freeCalc S) M ≃ S.Assignment M where
  toFun := restrict M
  invFun := extend M
  left_inv := extend_restrict M
  right_inv := restrict_extend M

/-- Uniqueness among all strict morphisms with the given primitive images. -/
theorem extend_unique (M : Calc.{u, v, z} V) (a : S.Assignment M)
    (F : Calc.Hom (freeCalc S) M) (h : restrict M F = a) : F = extend M a := by
  apply (homEquiv M).injective
  exact h.trans (restrict_extend M a).symm

/-- Restriction is natural under every strict map of target calculi. -/
theorem restrict_comp {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (F : Calc.Hom (freeCalc S) M) (k : Calc.Hom M N) :
    restrict N (F.comp k) = fun g => k.onOperation (restrict M F g) := rfl

/-- Extension is natural in the target, including targets in different universes. -/
theorem extend_natural_target {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (a : S.Assignment M) (k : Calc.Hom M N) :
    (extend M a).comp k = extend N (fun g => k.onOperation (a g)) := by
  apply extend_unique
  rw [restrict_comp, restrict_extend]

end Tree
end WitnessedDecompositions
