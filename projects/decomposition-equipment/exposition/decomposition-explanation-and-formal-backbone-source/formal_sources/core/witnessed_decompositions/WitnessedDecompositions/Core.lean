module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Logic.Equiv.Defs

/-!
# A path-typed calculus of witnessed decompositions

Interfaces are vertices of a quiver; components are its edges. A signature's
ordered input path and output edge have exactly the same outer endpoints.
Trees retain all generator witnesses. Substitution is occurrence-wise: its
recursive product has one independent replacement for every leaf occurrence.
No equation identifies differently grouped trees.
-/

@[expose] public section

universe u v w z

namespace WitnessedDecompositions

/-- A component with its two interface types retained. -/
structure Component (V : Type u) [Quiver.{v} V] where
  source : V
  target : V
  edge : source ⟶ target

namespace Path

variable {V : Type u} [Quiver.{v} V]

/-- Positions in a path, in the order in which its edges are traversed. -/
def Slot {a : V} : {b : V} → Quiver.Path a b → Type
  | _, .nil => Empty
  | _, .cons p _ => Sum (Slot p) Unit

/-- The endpoint-typed component at one position of a path. -/
def componentAt {a : V} : {b : V} → (p : Quiver.Path a b) → Slot p → Component V
  | _, .nil => fun i => nomatch i
  | _, @Quiver.Path.cons _ _ _ b c p e => fun i => match i with
      | .inl j => componentAt p j
      | .inr () => ⟨b, c, e⟩

/-- Replace every edge occurrence by a path with the same two endpoints. -/
def expand {a : V} : {b : V} → (p : Quiver.Path a b) →
    (∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target) → Quiver.Path a b
  | _, .nil, _ => .nil
  | _, .cons p _, f => (expand p (fun i => f (.inl i))).comp (f (.inr ()))

/-- Keep the ordered edge sequence, including the components' interface types. -/
def components {a : V} : {b : V} → Quiver.Path a b → List (Component V)
  | _, .nil => []
  | _, @Quiver.Path.cons _ _ _ b c p e => components p ++ [⟨b, c, e⟩]

@[simp] theorem components_comp {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) : components (p.comp q) = components p ++ components q := by
  induction q with
  | nil => simp [components]
  | cons q e ih => simp [components, ih, List.append_assoc]

/-- Concatenate lists assigned to path positions in their traversal order. -/
def collect {α : Type z} {a : V} : {b : V} → (p : Quiver.Path a b) →
    (Slot p → List α) → List α
  | _, .nil, _ => []
  | _, .cons p _, f => collect p (fun i => f (.inl i)) ++ f (.inr ())

@[simp] theorem components_expand {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target) :
    components (expand p f) = collect p (fun i => components (f i)) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change components ((expand p (fun i => f (.inl i))).comp (f (.inr ()))) = _
      exact (components_comp _ _).trans
        (congrArg (fun l => l ++ components (f (.inr ()))) (ih (fun i => f (.inl i))))

@[simp] theorem expand_edges {a b : V} (p : Quiver.Path a b) :
    expand p (fun i => (componentAt p i).edge.toPath) = p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [expand, componentAt, ih]

end Path

/-- Primitive decomposition witnesses. Empty inputs are necessarily endomorphisms:
`input g : Path a b` can be empty only if `a = b`. -/
structure Signature (V : Type u) [Quiver.{v} V] where
  Generator : Type w
  source : Generator → V
  target : Generator → V
  input : ∀ g, Quiver.Path (source g) (target g)
  output : ∀ g, source g ⟶ target g

namespace Signature

variable {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V)

/-- Output component of a primitive witness. -/
def result (g : S.Generator) : Component V := ⟨S.source g, S.target g, S.output g⟩

/-- Input component at a particular ordered occurrence. -/
def argument (g : S.Generator) (i : Path.Slot (S.input g)) : Component V :=
  Path.componentAt (S.input g) i

/-- Zero-input witnesses have equal outer interfaces. -/
theorem nullary_is_loop (g : S.Generator) (h : (S.input g).length = 0) :
    S.source g = S.target g := Quiver.Path.eq_of_length_zero (S.input g) h

end Signature

/-- Free witnessed trees. A leaf is the identity decomposition of its component.
The children of a node are independently indexed by occurrences of its input path. -/
inductive Tree {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V) :
    Component V → Type (max u v w) where
  | leaf (c : Component V) : Tree S c
  | node (g : S.Generator) (children : ∀ i : Path.Slot (S.input g),
      Tree S (S.argument g i)) : Tree S (S.result g)

namespace Tree

variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- The one-node tree of a primitive witness. -/
def corolla (g : S.Generator) : Tree S (S.result g) :=
  .node g (fun i => .leaf (S.argument g i))

/-- Primitive witnesses in preorder. This retains presentation information that
flattening is allowed to forget. -/
def generators : {c : Component V} → Tree S c → List S.Generator
  | _, .leaf _ => []
  | _, .node g children => g :: Path.collect (S.input g) (fun i => generators (children i))

/-- A simultaneous substitution has one replacement per leaf occurrence.
The products mirror only the *indexing* of leaves; the replacement trees may
have any shapes allowed by the signature. Equal component types do not force
equal replacements. -/
def Substitution : {c : Component V} → Tree S c → Type (max u v w)
  | _, .leaf c => Tree S c
  | _, .node _ children => ∀ i, Substitution (children i)

/-- Occurrence-wise, order-preserving grafting. -/
def graft : {c : Component V} → (t : Tree S c) → Substitution t → Tree S c
  | _, .leaf _, σ => σ
  | _, .node g children, σ => .node g (fun i => graft (children i) (σ i))

/-- The substitution which replaces each leaf by its identity tree. -/
def identity : {c : Component V} → (t : Tree S c) → Substitution t
  | _, .leaf c => .leaf c
  | _, .node _ children => fun i => identity (children i)

/-- Left unit: substituting into an identity tree returns the replacement. -/
@[simp] theorem graft_leaf (c : Component V) (t : Tree S c) :
    graft (Tree.leaf (S := S) c) t = t := rfl

/-- Right unit: grafting identity trees changes no presentation. -/
@[simp] theorem graft_identity {c : Component V} (t : Tree S c) :
    graft t (identity t) = t := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [graft, identity]
      congr 1
      funext i
      exact ih i

/-- Compose two layers of occurrence-wise substitutions. The second layer is
indexed by the leaves *after* the first graft, so its typing cannot omit a leaf
or accidentally identify two occurrences. -/
def compose : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    Substitution (graft t σ) → Substitution t
  | _, .leaf _, σ, τ => graft σ τ
  | _, .node _ children, σ, τ => fun i => compose (children i) (σ i) (τ i)

/-- Associativity of simultaneous substitution, with the second-layer leaves
matched by the structural dependent product rather than by equality of colors. -/
theorem graft_assoc {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) :
    graft (graft t σ) τ = graft t (compose t σ τ) := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [graft, compose]
      congr 1
      funext i
      exact ih i (σ i) (τ i)

@[simp] theorem compose_identity {c : Component V} (t : Tree S c)
    (σ : Substitution t) : compose t σ (identity (graft t σ)) = σ := by
  induction t with
  | leaf c => exact graft_identity σ
  | node g children ih =>
      funext i
      exact ih i (σ i)

/-- Leaf occurrences, not just the set or multiset of component types. -/
def Leaf : {c : Component V} → Tree S c → Type
  | _, .leaf _ => Unit
  | _, .node _ children => (i : _) × Leaf (children i)

/-- Component type of a leaf occurrence. -/
def leafComponent : {c : Component V} → (t : Tree S c) → Leaf t → Component V
  | _, .leaf c => fun _ => c
  | _, .node _ children => fun ⟨i, j⟩ => leafComponent (children i) j

/-- Turn an explicitly occurrence-indexed assignment into a structural substitution. -/
def fromLeaves : {c : Component V} → (t : Tree S c) →
    (∀ l : Leaf t, Tree S (leafComponent t l)) → Substitution t
  | _, .leaf _, f => f ()
  | _, .node _ children, f => fun i => fromLeaves (children i) (fun j => f ⟨i, j⟩)

/-- Read a structural substitution at an individual leaf occurrence. -/
def atLeaf : {c : Component V} → (t : Tree S c) → Substitution t →
    (l : Leaf t) → Tree S (leafComponent t l)
  | _, .leaf _, σ => fun _ => σ
  | _, .node _ children, σ => fun ⟨i, j⟩ => atLeaf (children i) (σ i) j

@[simp] theorem atLeaf_fromLeaves {c : Component V} (t : Tree S c)
    (f : ∀ l : Leaf t, Tree S (leafComponent t l)) (l : Leaf t) :
    atLeaf t (fromLeaves t f) l = f l := by
  induction t with
  | leaf c => cases l; rfl
  | node g children ih =>
      rcases l with ⟨i, j⟩
      exact ih i (fun j => f ⟨i, j⟩) j

@[simp] theorem fromLeaves_atLeaf {c : Component V} (t : Tree S c)
    (σ : Substitution t) : fromLeaves t (atLeaf t σ) = σ := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      funext i
      exact ih i (σ i)

/-- There is exactly one independent replacement tree for each leaf occurrence. -/
def substitutionEquiv {c : Component V} (t : Tree S c) :
    Substitution t ≃ (∀ l : Leaf t, Tree S (leafComponent t l)) where
  toFun := atLeaf t
  invFun := fromLeaves t
  left_inv := fromLeaves_atLeaf t
  right_inv f := funext (atLeaf_fromLeaves t f)

/-- The evaluated flat decomposition. The result is a genuine quiver path with
the same outer interfaces as the output component, not an untyped list. -/
def frontier : {c : Component V} → Tree S c → Quiver.Path c.source c.target
  | _, .leaf c => c.edge.toPath
  | _, .node g children => Path.expand (S.input g) (fun i => frontier (children i))

@[simp] theorem frontier_corolla (g : S.Generator) :
    frontier (corolla g) = S.input g :=
  Path.expand_edges (S.input g)

/-- Ordered leaf components, defined independently of the flattened path. -/
def leaves : {c : Component V} → Tree S c → List (Component V)
  | _, .leaf c => [c]
  | _, .node g children => Path.collect (S.input g) (fun i => leaves (children i))

/-- Flattening keeps every leaf once, in its original planar order. -/
theorem frontier_components {c : Component V} (t : Tree S c) :
    Path.components (frontier t) = leaves t := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      change Path.components (Path.expand (S.input g) (fun i => frontier (children i))) = _
      exact (Path.components_expand (S.input g) (fun i => frontier (children i))).trans
        (congrArg (Path.collect (S.input g)) (funext ih))

/-- Ordered flattening of the replacement frontier at every original leaf. -/
def substitutionLeaves : {c : Component V} → (t : Tree S c) →
    Substitution t → List (Component V)
  | _, .leaf _, σ => leaves σ
  | _, .node g children, σ =>
      Path.collect (S.input g) (fun i => substitutionLeaves (children i) (σ i))

/-- Grafting concatenates replacement frontiers in the original leaf order.
It uses every replacement exactly once, without permutation. A nullary
replacement legitimately contributes no leaves. -/
theorem leaves_graft {c : Component V} (t : Tree S c) (σ : Substitution t) :
    leaves (graft t σ) = substitutionLeaves t σ := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [graft, leaves, substitutionLeaves]
      congr 1
      funext i
      exact ih i (σ i)

/-- The path obtained by concatenating the replacement frontiers in the
original occurrence order. This is defined directly on the substitution. -/
def substitutionFrontier : {c : Component V} → (t : Tree S c) →
    Substitution t → Quiver.Path c.source c.target
  | _, .leaf _, σ => frontier σ
  | _, .node g children, σ =>
      Path.expand (S.input g) (fun i => substitutionFrontier (children i) (σ i))

/-- Evaluation of a graft is exactly substitution of the replacement frontiers. -/
theorem frontier_graft {c : Component V} (t : Tree S c) (σ : Substitution t) :
    frontier (graft t σ) = substitutionFrontier t σ := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [graft, frontier, substitutionFrontier]
      congr 1
      funext i
      exact ih i (σ i)

/-- Path-indexed operations: the fiber of witnessed trees over a fixed typed
input path. Equality here is equality of presentation trees, not merely of paths. -/
def Operation (c : Component V) (p : Quiver.Path c.source c.target) :=
  {t : Tree S c // frontier t = p}

/-- Every tree determines its path-typed operation without losing witnesses. -/
def operation {c : Component V} (t : Tree S c) : Operation (S := S) c (frontier t) :=
  ⟨t, rfl⟩

/-- Grafting lands in the fiber specified by the substituted typed frontier.
The composition laws above are stated on the underlying occurrence-indexed
trees; this does not package a separate multicategory typeclass. -/
def graftOperation {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p) (σ : Substitution t.val) :
    Operation (S := S) c (substitutionFrontier t.val σ) :=
  ⟨graft t.val σ, frontier_graft t.val σ⟩

end Tree

/-- A target interpretation: one carrier per component and an ordered operation
for each primitive witness. This is not an assumption that every such algebra
forgets grouping. -/
structure Algebra {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V) where
  Carrier : Component V → Type z
  generator : ∀ g, (∀ i : Path.Slot (S.input g), Carrier (S.argument g i)) →
    Carrier (S.result g)

namespace Algebra

variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Evaluate a witnessed tree in a chosen algebra and chosen leaf interpretation. -/
def evaluate (A : Algebra.{u, v, w, z} S) (atom : ∀ c, A.Carrier c) :
    {c : Component V} → Tree S c → A.Carrier c
  | _, .leaf c => atom c
  | _, .node g children => A.generator g (fun i => evaluate A atom (children i))

/-- Uniqueness of the structural fold into a component-indexed algebra with
one chosen atom per component. This is not a universal-property theorem in
a separately defined category of multicategories. -/
theorem evaluate_unique (A : Algebra.{u, v, w, z} S) (atom : ∀ c, A.Carrier c)
    (f : ∀ {c}, Tree S c → A.Carrier c)
    (hLeaf : ∀ c, f (.leaf c) = atom c)
    (hNode : ∀ g children, f (.node g children) = A.generator g (fun i => f (children i)))
    {c : Component V} (t : Tree S c) : f t = evaluate A atom t := by
  induction t with
  | leaf c => exact hLeaf c
  | node g children ih =>
      rw [hNode]
      simp only [evaluate]
      congr 1
      funext i
      exact ih i

/-- A witness-retaining interpretation, in contrast to flattening. -/
def presentation : Algebra S where
  Carrier := Tree S
  generator := Tree.node

/-- Evaluating in syntax itself preserves every witness and grouping. -/
@[simp] theorem evaluate_presentation {c : Component V} (t : Tree S c) :
    evaluate (presentation (S := S)) Tree.leaf t = t := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [evaluate, presentation]
      congr 1
      funext i
      exact ih i

/-- The flattening algebra remembers ordered component edges and interfaces,
but intentionally forgets the internal primitive witnesses and groupings. -/
def flattening : Algebra S where
  Carrier c := Quiver.Path c.source c.target
  generator g children := Path.expand (S.input g) children

@[simp] theorem evaluate_flattening {c : Component V} (t : Tree S c) :
    evaluate (flattening (S := S)) (fun c => c.edge.toPath) t = Tree.frontier t := by
  induction t with
  | leaf c => rfl
  | node g children ih =>
      simp only [evaluate, flattening, Tree.frontier]
      congr 1
      funext i
      exact ih i

end Algebra

end WitnessedDecompositions
