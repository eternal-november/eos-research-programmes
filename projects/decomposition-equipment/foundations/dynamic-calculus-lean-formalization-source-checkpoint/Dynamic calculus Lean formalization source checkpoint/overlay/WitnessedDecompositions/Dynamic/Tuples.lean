module

public import WitnessedDecompositions.Dynamic.Graph

/-!
# Compatible tuple graphs and actual graph-map witnesses

The recursive carrier is an explicit implementation of a finite compatible
ordered tuple. Its universal property below uses the original `Path.Slot`
family, so neither colors nor repeated occurrences are identified. Empty
profiles retain the boundary graph itself, not a terminal singleton. No
substitution proof identifies differently parenthesized pullbacks by reflexivity.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u v w
namespace WitnessedDecompositions.Dynamic

structure Span (A B : Graph.{w}) where
  graph : Graph.{w}
  left : Graph.Hom graph A
  right : Graph.Hom graph B

namespace Assignment
variable {V : Type u} [Quiver.{v} V]

/-- The nil graph is the actual boundary graph. Nonempty carriers retain
compatible state tuples and compatible actual-event tuples. -/
def tupleSpan (D : Assignment.{u, v, w} V) {a : V} :
    {b : V} → Quiver.Path a b → Span (D.boundary a) (D.boundary b)
  | _, .nil => ⟨D.boundary a, Graph.Hom.id _, Graph.Hom.id _⟩
  | _, @Quiver.Path.cons _ _ _ b c p e =>
      let P := D.tupleSpan p
      let C : Component V := ⟨b, c, e⟩
      ⟨Graph.pullback P.right (D.left C),
       (Graph.pullback.fst P.right (D.left C)).comp P.left,
       (Graph.pullback.snd P.right (D.left C)).comp (D.right C)⟩

abbrev tupleGraph (D : Assignment.{u, v, w} V) {a b : V} (p : Quiver.Path a b) :=
  (D.tupleSpan p).graph
abbrev tupleLeft (D : Assignment.{u, v, w} V) {a b : V} (p : Quiver.Path a b) :=
  (D.tupleSpan p).left
abbrev tupleRight (D : Assignment.{u, v, w} V) {a b : V} (p : Quiver.Path a b) :=
  (D.tupleSpan p).right

/-- Read every coordinate graph map, indexed by the original ordered slots. -/
def coordinates (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V} :
    {b : V} → (p : Quiver.Path a b) → Graph.Hom X (D.tupleGraph p) → D.Family X p
  | _, .nil, _ => fun i => nomatch i
  | _, .cons p _, m => fun i => match i with
      | .inl j => D.coordinates p (m.comp (Graph.pullback.fst _ _)) j
      | .inr () => m.comp (Graph.pullback.snd _ _)

/-- Reading coordinates preserves all fine boundary equations. -/
theorem coordinates_compatible (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) (m : Graph.Hom X (D.tupleGraph p)) :
    D.Compatible X p (D.coordinates p m)
      (m.comp (D.tupleLeft p)) (m.comp (D.tupleRight p)) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      refine ⟨?_, rfl⟩
      have h := ih (m.comp (Graph.pullback.fst _ _))
      have hc := congrArg (fun f => m.comp f)
        (Graph.pullback.condition (D.tupleRight p) (D.left ⟨_, _, e⟩))
      change D.Compatible X p (D.coordinates p (m.comp (Graph.pullback.fst _ _)))
        ((m.comp (Graph.pullback.fst _ _)).comp (D.tupleLeft p))
        ((m.comp (Graph.pullback.snd _ _)).comp (D.left ⟨_, _, e⟩))
      rw [Graph.Hom.comp_assoc, Graph.Hom.comp_assoc] at h ⊢
      rw [hc] at h
      exact h

/-- A witness is an actual graph map with its two specified outer legs. -/
def BoundaryMap (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a b : V}
    (p : Quiver.Path a b) (h : Graph.Hom X (D.boundary a))
    (k : Graph.Hom X (D.boundary b)) :=
  {m : Graph.Hom X (D.tupleGraph p) //
    m.comp (D.tupleLeft p) = h ∧ m.comp (D.tupleRight p) = k}

/-- Assemble a graph map from its full compatible occurrence family. -/
def assemble (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V} :
    {b : V} → (p : Quiver.Path a b) → (f : D.Family X p) →
    (h : Graph.Hom X (D.boundary a)) → (k : Graph.Hom X (D.boundary b)) →
    D.Compatible X p f h k → D.BoundaryMap p h k
  | _, .nil, _, h, _, hc => ⟨h, rfl, hc⟩
  | _, .cons p _, f, h, k, hc =>
      let pref := D.assemble p (fun i => f (.inl i)) h
        ((f (.inr ())).comp (D.left _)) hc.1
      let m := Graph.pullback.lift _ _ pref.val (f (.inr ())) pref.property.2
      ⟨m, by
        change (m.comp (Graph.pullback.fst _ _)).comp (D.tupleLeft p) = h
        exact pref.property.1,
       by
        change (m.comp (Graph.pullback.snd _ _)).comp (D.right _) = k
        exact hc.2⟩

@[simp] theorem coordinates_assemble (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) (f : D.Family X p)
    (h : Graph.Hom X (D.boundary a)) (k : Graph.Hom X (D.boundary b))
    (hc : D.Compatible X p f h k) :
    D.coordinates p (D.assemble p f h k hc).val = f := by
  induction p with
  | nil => funext i; exact nomatch i
  | cons p e ih =>
      funext i
      cases i with
      | inl i => exact congrFun (ih (fun j => f (.inl j))
          ((f (.inr ())).comp (D.left _)) hc.1) i
      | inr i => cases i; rfl

/-- The coordinates together with the retained left boundary determine the map.
The boundary hypothesis is essential precisely in the empty-profile case. -/
theorem coordinates_ext (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) {m n : Graph.Hom X (D.tupleGraph p)}
    (hl : m.comp (D.tupleLeft p) = n.comp (D.tupleLeft p))
    (hf : D.coordinates p m = D.coordinates p n) : m = n := by
  induction p with
  | nil => exact hl
  | cons p e ih =>
      apply Graph.pullback.hom_ext
      · apply ih
        · exact hl
        · funext i
          exact congrFun hf (.inl i)
      · exact congrFun hf (.inr ())

/-- Full equivalence, not only an image or trace-level comparison. -/
def compatibleFamilyEquiv (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b)
    (h : Graph.Hom X (D.boundary a)) (k : Graph.Hom X (D.boundary b)) :
    {f : D.Family X p // D.Compatible X p f h k} ≃ D.BoundaryMap p h k where
  toFun f := D.assemble p f.val h k f.property
  invFun m := ⟨D.coordinates p m.val, by
    have hc := D.coordinates_compatible p m.val
    rw [m.property.1, m.property.2] at hc
    exact hc⟩
  left_inv f := by
    apply Subtype.ext
    exact D.coordinates_assemble p f.val h k f.property
  right_inv m := by
    apply Subtype.ext
    apply D.coordinates_ext p
    · exact (D.assemble p _ h k _).property.1.trans m.property.1.symm
    · exact D.coordinates_assemble p _ h k _

/-- Canonical singleton tuple map. The redundant interface coordinate is
supplied by the actual component's left leg. -/
def tupleSingleton (D : Assignment.{u, v, w} V) (c : Component V) :
    Graph.Hom (D.component c) (D.tupleGraph c.edge.toPath) :=
  Graph.pullback.lift (Graph.Hom.id _) (D.left c)
    (D.left c) (Graph.Hom.id _) rfl

/-- The inverse forgets the redundant interface coordinate, not an event record. -/
def tupleSingletonInverse (D : Assignment.{u, v, w} V) (c : Component V) :
    Graph.Hom (D.tupleGraph c.edge.toPath) (D.component c) :=
  Graph.pullback.snd (Graph.Hom.id _) (D.left c)

@[simp] theorem tupleSingleton_left (D : Assignment.{u, v, w} V) (c : Component V) :
    (D.tupleSingleton c).comp (D.tupleLeft c.edge.toPath) = D.left c := rfl

@[simp] theorem tupleSingleton_right (D : Assignment.{u, v, w} V) (c : Component V) :
    (D.tupleSingleton c).comp (D.tupleRight c.edge.toPath) = D.right c := rfl

@[simp] theorem tupleSingleton_inverse (D : Assignment.{u, v, w} V) (c : Component V) :
    (D.tupleSingleton c).comp (D.tupleSingletonInverse c) = Graph.Hom.id _ := rfl

@[simp] theorem tupleSingletonInverse_inverse (D : Assignment.{u, v, w} V)
    (c : Component V) :
    (D.tupleSingletonInverse c).comp (D.tupleSingleton c) = Graph.Hom.id _ := by
  apply Graph.pullback.hom_ext
  · exact (Graph.pullback.condition (Graph.Hom.id _) (D.left c)).symm
  · rfl

/-- Singleton identification is an actual graph isomorphism on both sorts. -/
theorem tupleSingleton_isIso (D : Assignment.{u, v, w} V) (c : Component V) :
    Graph.IsIso (D.tupleSingleton c) :=
  ⟨D.tupleSingletonInverse c, D.tupleSingleton_inverse c,
    D.tupleSingletonInverse_inverse c⟩

/-- Nil retains its actual boundary graph definitionally. -/
@[simp] theorem tupleGraph_nil (D : Assignment.{u, v, w} V) (a : V) :
    D.tupleGraph (Quiver.Path.nil : Quiver.Path a a) = D.boundary a := rfl

/-- There is an empty-profile map exactly when its two legs agree. -/
theorem nullary_nonempty_iff (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V}
    (h k : Graph.Hom X (D.boundary a)) :
    Nonempty (D.BoundaryMap (Quiver.Path.nil : Quiver.Path a a) h k) ↔ h = k := by
  constructor
  · rintro ⟨m⟩
    exact m.property.1.symm.trans m.property.2
  · intro he
    exact ⟨⟨h, rfl, he⟩⟩

/-- A nullary witness is the common leg itself, not a constant map to a singleton. -/
theorem nullary_map_eq (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V}
    (h k : Graph.Hom X (D.boundary a))
    (m : D.BoundaryMap (Quiver.Path.nil : Quiver.Path a a) h k) : m.val = h :=
  m.property.1

instance nullary_subsingleton (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V}
    (h k : Graph.Hom X (D.boundary a)) :
    Subsingleton (D.BoundaryMap (Quiver.Path.nil : Quiver.Path a a) h k) where
  allEq m n := Subtype.ext (m.property.1.trans n.property.1.symm)

/-- Exact nullary witnesses are exactly isomorphisms of the common leg. -/
theorem nullary_exact_iff (D : Assignment.{u, v, w} V) {X : Graph.{w}} {a : V}
    (h k : Graph.Hom X (D.boundary a))
    (m : D.BoundaryMap (Quiver.Path.nil : Quiver.Path a a) h k) :
    Graph.IsIso m.val ↔ Graph.IsIso h := by
  rw [D.nullary_map_eq h k m]

end Assignment
end WitnessedDecompositions.Dynamic
