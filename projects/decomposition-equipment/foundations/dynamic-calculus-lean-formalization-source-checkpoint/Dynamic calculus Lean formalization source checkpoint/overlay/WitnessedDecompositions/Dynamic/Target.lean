module
public import WitnessedDecompositions.Dynamic.MapOperations
public import WitnessedDecompositions.Dynamic.Compatibility
public import WitnessedDecompositions.Dynamic.Tuples
/-!
# The actual graph-span dynamic target calculus

Operations retain the original typed profile, every actual coordinate graph map,
and fine boundary equations. No exactness condition is imposed. Nullary operations
retain the common map into the actual boundary graph through `witness`.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u v w
namespace WitnessedDecompositions.Dynamic.Assignment
open Path
variable {V : Type u} [Quiver.{v} V] (D : Assignment.{u,v,w} V)

/-- All boundary-compatible graph-map operations, not only exact decompositions. -/
def Op (c : Component V) :=
  {a : D.MapOp c // D.Compatible (D.component c) a.profile a.maps (D.left c) (D.right c)}

namespace Op
variable {D}
abbrev profile {c : Component V} (a : D.Op c) := a.val.profile
abbrev maps {c : Component V} (a : D.Op c) := a.val.maps

def identity (c : Component V) : D.Op c :=
  ⟨MapOp.identity c, And.intro rfl rfl⟩

def subst {c : Component V} (a : D.Op c)
    (f : ∀ i : Slot a.profile, D.Op (componentAt a.profile i)) : D.Op c :=
  ⟨MapOp.subst a.val (fun i => (f i).val),
    D.compatible_joinFamily a.profile a.maps (D.left c) (D.right c) a.property
      (fun i => (f i).profile) (fun i => (f i).maps) (fun i => (f i).property)⟩

/-- The full witness graph map, including the retained boundary map when nil. -/
def witness {c : Component V} (a : D.Op c) :
    D.BoundaryMap a.profile (D.left c) (D.right c) :=
  D.assemble a.profile a.maps (D.left c) (D.right c) a.property

/-- Exactness is a marking of operations, not a restriction on the target. -/
def Exact {c : Component V} (a : D.Op c) : Prop := Graph.IsIso a.witness.val

/-- The singleton tuple comparison makes the actual identity witness exact. -/
theorem identity_exact (c : Component V) : (identity (D := D) c).Exact :=
  D.tupleSingleton_isIso c

end Op

def collection : Collection V where
  Op := D.Op
  profile a := a.profile

def calcData : CalcData V where
  toCollection := D.collection
  identity := Op.identity
  profile_identity _ := rfl
  subst := Op.subst
  profile_subst _ _ := rfl

/-- The original `Calc`, with arbitrary nullary and repeated-occurrence substitution. -/
def calculus : Calc V where
  toCalcData := D.calcData
  subst_identity a := by
    apply Subtype.ext
    exact MapOp.subst_identity a.val
  identity_subst a := by
    apply Subtype.ext
    refine Eq.trans ?_ (MapOp.identity_subst a.val)
    apply congrArg (MapOp.subst (MapOp.identity _))
    funext i
    rcases i with i | ⟨⟩
    · exact nomatch i
    · rfl
  subst_assoc a f h := by
    apply Subtype.ext
    change MapOp.subst (MapOp.subst a.val (fun i => (f i).val))
      (fun k => (h k).val) = _
    rw [MapOp.subst_assoc]
    congr 1
    funext i
    change MapOp.subst (f i).val
      (expandFamily D.MapOp a.profile (fun i => (f i).profile) (fun k => (h k).val) i) =
      MapOp.subst (f i).val (fun j =>
        (expandFamily D.Op a.profile (fun i => (f i).profile) h i j).val)
    apply congrArg (MapOp.subst (f i).val)
    funext j
    exact (Path.expandFamily_natural D.Op D.MapOp (fun _ x => x.val)
      a.profile (fun i => (f i).profile) h i j).symm

/-- Forget only the compatibility proofs; actual operations/maps are retained. -/
def inclusion : Calc.Hom D.calculus (MapOp.calculus (D := D)) where
  map a := a.val
  profile_map _ := rfl
  map_identity _ := rfl
  map_subst _ _ := rfl

/-- A concrete operation at a prescribed original profile. -/
def operation {c : Component V} (p : Quiver.Path c.source c.target)
    (f : D.Family (D.component c) p)
    (hf : D.Compatible (D.component c) p f (D.left c) (D.right c)) :
    D.calculus.Operation c p := ⟨⟨⟨p,f⟩,hf⟩,rfl⟩

/-- The target's prescribed fibre is exactly all boundary-preserving graph maps. -/
def operationEquiv (c : Component V) (p : Quiver.Path c.source c.target) :
    D.calculus.Operation c p ≃ D.BoundaryMap p (D.left c) (D.right c) :=
  (show D.calculus.Operation c p ≃
      {f : D.Family (D.component c) p // D.Compatible (D.component c) p f (D.left c) (D.right c)} from
    { toFun := fun a => ⟨a.property ▸ a.val.maps, by
        rcases a with ⟨⟨⟨q,f⟩,hf⟩,hp⟩
        cases hp
        exact hf⟩
      invFun := fun f => D.operation p f.val f.property
      left_inv := by
        rintro ⟨⟨⟨q,f⟩,hf⟩,hp⟩
        cases hp
        rfl
      right_inv := by rintro ⟨f,hf⟩; rfl }).trans
    (D.compatibleFamilyEquiv p (D.left c) (D.right c))

/-- The nil operation fibre is inhabited precisely when the two actual legs agree. -/
theorem nullary_operation_nonempty_iff {v : V} (e : v ⟶ v) :
    Nonempty (D.calculus.Operation ⟨v,v,e⟩ .nil) ↔ D.left ⟨v,v,e⟩ = D.right ⟨v,v,e⟩ := by
  constructor
  · rintro ⟨a⟩
    exact (D.nullary_nonempty_iff _ _).1 ⟨D.operationEquiv _ _ a⟩
  · intro h
    obtain ⟨m⟩ := (D.nullary_nonempty_iff _ _).2 h
    exact ⟨(D.operationEquiv _ _).symm m⟩

instance nullary_operation_subsingleton {v : V} (e : v ⟶ v) :
    Subsingleton (D.calculus.Operation ⟨v,v,e⟩ .nil) :=
  ⟨fun _ _ => (D.operationEquiv _ _).injective (Subsingleton.elim _ _)⟩

/-- In a nullary fibre, exactness tests the common boundary leg itself. -/
theorem nullary_operation_exact_iff {v : V} (e : v ⟶ v)
    (a : D.calculus.Operation ⟨v,v,e⟩ .nil) :
    Graph.IsIso (D.operationEquiv _ _ a).val ↔ Graph.IsIso (D.left ⟨v,v,e⟩) :=
  D.nullary_exact_iff _ _ _

/-- The equivalence is the same actual witness map, after the advertised profile equality. -/
theorem operationEquiv_witness (c : Component V) (p : Quiver.Path c.source c.target)
    (a : D.calculus.Operation c p) :
    HEq (D.operationEquiv c p a).val a.val.witness.val := by
  rcases a with ⟨⟨⟨q,f⟩,hf⟩,hp⟩
  cases hp
  rfl

/-- The actual empty-profile map is forced to be the common original boundary leg. -/
theorem nullary_operation_map_eq {v : V} (e : v ⟶ v)
    (a : D.calculus.Operation ⟨v,v,e⟩ .nil) :
    (D.operationEquiv _ _ a).val = D.left ⟨v,v,e⟩ :=
  D.nullary_map_eq _ _ _

/-- Equivalent exactness statement directly on the target operation marking. -/
theorem nullary_exact_iff_leg {v : V} (e : v ⟶ v)
    (a : D.calculus.Operation ⟨v,v,e⟩ .nil) :
    a.val.Exact ↔ Graph.IsIso (D.left ⟨v,v,e⟩) := by
  have h := D.nullary_operation_exact_iff e a
  rcases a with ⟨⟨⟨q,f⟩,hf⟩,hp⟩
  cases hp
  exact h

end WitnessedDecompositions.Dynamic.Assignment
