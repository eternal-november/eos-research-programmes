import research.workstream_C2.lean.RelationInterface
import WitnessedDecompositions.RefinementFunctoriality
import WitnessedDecompositions.WeightInvariant

/-! E1's checked core-facing fragment. A concrete Nat-decorated relation equipment,
not a generic Calc renamed as equipment. Vertical maps are arbitrary functions;
cell witnesses retain an independent natural scalar, including at arity zero.
The full classical equipment/2-category package is proved separately in P.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace E1RelationEquipment
open WitnessedDecompositions
universe u v
variable {I : Type u} {X : I → Type v}
abbrev V := RelationInterface.Interface I X
abbrev Carrier (a : V (X := X)) := X a.label

/-- Actual equipment multicells: specified arbitrary vertical sides and a
retained scalar; the relation condition alone is proof-irrelevant. -/
structure Cell {a b c d : V (X := X)} (p : Quiver.Path a b) (H : c ⟶ d)
    (f : Carrier a → Carrier c) (g : Carrier b → Carrier d) where
  weight : Nat
  valid : ∀ x y, RelationInterface.evaluate p x y → H (f x) (g y)

@[ext] theorem Cell.ext {a b c d : V (X := X)} {p : Quiver.Path a b} {H : c ⟶ d}
    {f : Carrier a → Carrier c} {g : Carrier b → Carrier d}
    {α β : Cell p H f g} (h : α.weight = β.weight) : α = β := by
  cases α; cases β; cases h; rfl

def restrict {a b c d : V (X := X)} (H : c ⟶ d)
    (f : Carrier a → Carrier c) (g : Carrier b → Carrier d) : a ⟶ b :=
  fun x y => H (f x) (g y)

def restrictionCell {a b c d : V (X := X)} (H : c ⟶ d)
    (f : Carrier a → Carrier c) (g : Carrier b → Carrier d) :
    Cell (restrict H f g).toPath H f g :=
  ⟨0, by intro x y h; rw [RelationInterface.evaluate_edge] at h; exact h⟩

/-- Cartesian factorization for every actual original typed path, including nil.
This is an equivalence of complete cell data, not just existence/endpoint relabeling. -/
def restrictionEquiv {a b c d e f' : V (X := X)} (p : Quiver.Path a b)
    (H : e ⟶ f') (f : Carrier c → Carrier e) (g : Carrier d → Carrier f')
    (h : Carrier a → Carrier c) (k : Carrier b → Carrier d) :
    Cell p H (f ∘ h) (g ∘ k) ≃ Cell p (restrict H f g) h k where
  toFun α := ⟨α.weight, α.valid⟩
  invFun α := ⟨α.weight, α.valid⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Vertical composition coherence is literal for this split inverse-image cleavage. -/
theorem restrict_composite {a b c d e f' : V (X := X)} (H : e ⟶ f')
    (f : Carrier c → Carrier e) (g : Carrier d → Carrier f')
    (h : Carrier a → Carrier c) (k : Carrier b → Carrier d) :
    restrict (restrict H f g) h k = restrict H (f ∘ h) (g ∘ k) := rfl

theorem restrict_identity {a b : V (X := X)} (H : a ⟶ b) :
    restrict H id id = H := rfl

/-- Precomposition by an arbitrary semantic row, with its entire scalar retained.
Every well-typed multicell substitution row induces such a map on path composites. -/
def precompose {a b c d e f' : V (X := X)}
    {p : Quiver.Path a b} {q : Quiver.Path c d} {H : e ⟶ f'}
    {f : Carrier a → Carrier e} {g : Carrier b → Carrier f'}
    (α : Cell p H f g) (h : Carrier c → Carrier a) (k : Carrier d → Carrier b)
    (row : ∀ x y, RelationInterface.evaluate q x y → RelationInterface.evaluate p (h x) (k y)) (n : Nat) :
    Cell q H (f ∘ h) (g ∘ k) :=
  ⟨α.weight + n, fun x y hxy => α.valid _ _ (row x y hxy)⟩

/-- Cartesian factorization commutes with precomposition in arbitrary path contexts. -/
theorem restriction_natural {a b c d e f' j l : V (X := X)}
    {p : Quiver.Path a b} {q : Quiver.Path c d} {H : j ⟶ l}
    (f : Carrier e → Carrier j) (g : Carrier f' → Carrier l)
    (h : Carrier a → Carrier e) (k : Carrier b → Carrier f')
    (α : Cell p H (f ∘ h) (g ∘ k))
    (r : Carrier c → Carrier a) (s : Carrier d → Carrier b)
    (row : ∀ x y, RelationInterface.evaluate q x y → RelationInterface.evaluate p (r x) (s y)) (n : Nat) :
    restrictionEquiv q H f g (h ∘ r) (k ∘ s) (precompose α r s row n) =
      precompose (restrictionEquiv p H f g h k α) r s row n := rfl

/-- The nullary source at a is not an augmented nullary target. -/
def unitCell (a : V (X := X)) : Cell (Quiver.Path.nil : Quiver.Path a a) (RelationInterface.diagonal a) id id :=
  ⟨0, fun _ _ h => h⟩

def nullaryPrimitive (a : V (X := X)) (n : Nat) :
    Cell (Quiver.Path.nil : Quiver.Path a a) (RelationInterface.diagonal a) id id :=
  ⟨n, fun _ _ h => h⟩

theorem primitive_not_unit (a : V (X := X)) : nullaryPrimitive a 1 ≠ unitCell a := by
  intro h
  have := congrArg Cell.weight h
  contradiction

/-- Unit insertion at ANY specified junction, with arbitrary prefix/suffix. -/
theorem evaluate_unit_context {a b c : V (X := X)} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    RelationInterface.evaluate ((p.comp (RelationInterface.diagonal b).toPath).comp q) = RelationInterface.evaluate (p.comp q) := by
  rw [RelationInterface.evaluate_comp, RelationInterface.evaluate_comp, RelationInterface.evaluate_edge, RelationInterface.comp_diagonal_right, RelationInterface.evaluate_comp]

def unitContextEquiv {a b c d e : V (X := X)} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (H : d ⟶ e) (f : Carrier a → Carrier d) (g : Carrier c → Carrier e) :
    Cell ((p.comp (RelationInterface.diagonal b).toPath).comp q) H f g ≃ Cell (p.comp q) H f g where
  toFun α := ⟨α.weight, by rw [← evaluate_unit_context p q]; exact α.valid⟩
  invFun α := ⟨α.weight, by rw [evaluate_unit_context p q]; exact α.valid⟩
  left_inv _ := Cell.ext rfl
  right_inv _ := Cell.ext rfl

/-- Universal-unit substitution preserves every parallel scalar. -/
theorem unit_context_weight {a b c d e : V (X := X)} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (H : d ⟶ e) (f : Carrier a → Carrier d) (g : Carrier c → Carrier e)
    (α : Cell ((p.comp (RelationInterface.diagonal b).toPath).comp q) H f g) :
    (unitContextEquiv p q H f g α).weight = α.weight := rfl

/-- Substituting the scalar-one primitive misses scalar zero, hence is NOT universal. -/
theorem primitive_substitution_not_surjective : ¬ Function.Surjective (fun n : Nat => n + 1) := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  change n + 1 = 0 at hn
  omega

/-- Totalization of the ACTUAL globular Cell fibres in the fixed original API. -/
structure CoreOp (c : Component (V (X := X))) where
  profile : Quiver.Path c.source c.target
  cell : Cell profile c.edge id id

@[ext] theorem CoreOp.ext {c : Component (V (X := X))} {a b : CoreOp c}
    (hp : a.profile = b.profile) (hw : a.cell.weight = b.cell.weight) : a = b := by
  cases a with | mk p α =>
    cases b with | mk q β =>
      dsimp at hp
      cases hp
      have h : α = β := Cell.ext hw
      cases h
      rfl

def coreData : CalcData (V (X := X)) where
  Op := CoreOp
  profile a := a.profile
  identity c := ⟨c.edge.toPath, 0, by intro x y h; rwa [RelationInterface.evaluate_edge] at h⟩
  profile_identity _ := rfl
  subst a f := ⟨Path.expand a.profile (fun i => (f i).profile),
    a.cell.weight + Path.sum a.profile (fun i => (f i).cell.weight),
    fun x y h => a.cell.valid x y (RelationInterface.evaluate_expand_le a.profile
      (fun i => (f i).profile) (fun i => (f i).cell.valid) x y h)⟩
  profile_subst _ _ := rfl

theorem sum_zero {a b : V (X := X)} (p : Quiver.Path a b) : Path.sum p (fun _ => 0) = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [Path.sum_cons, ih]

theorem weight_transport {c d : Component (V (X := X))} (h : c = d) (a : CoreOp c) :
    (Path.occurrenceTransport CoreOp h a).cell.weight = a.cell.weight := by cases h; rfl

/-- This lawful Calc is obtained from concrete equipment globular cells. -/
def coreCalc : Calc (V (X := X)) where
  toCalcData := coreData
  subst_identity a := by
    apply CoreOp.ext
    · exact Path.expand_edges a.profile
    · change a.cell.weight + Path.sum a.profile (fun _ => 0) = a.cell.weight
      rw [sum_zero, Nat.add_zero]
  identity_subst a := by
    apply CoreOp.ext
    · exact Quiver.Path.nil_comp a.profile
    · simp [coreData, Collection.singletonFamily, Path.sum, Path.collect, Quiver.Hom.toPath]
  subst_assoc a f h := by
    apply CoreOp.ext
    · exact coreData.composeAt_profile f h
    · change (a.cell.weight + Path.sum a.profile (fun i => (f i).cell.weight)) +
        Path.sum (Path.expand a.profile (fun i => (f i).profile)) (fun j => (h j).cell.weight) =
        a.cell.weight + Path.sum a.profile (fun i => (f i).cell.weight +
          Path.sum (f i).profile (fun j =>
            (Path.expandFamily CoreOp a.profile (fun i => (f i).profile) h i j).cell.weight))
      rw [Path.sum_add, Nat.add_assoc]
      congr 1
      congr 1
      rw [Path.sum_expand]
      congr 1
      funext i
      congr 1
      funext j
      exact (weight_transport _ _).symm

/-- Exact image statement: every globular equipment cell, with its actual scalar,
is represented uniquely by an original prescribed-profile operation. -/
def coreFiberEquiv (c : Component (V (X := X))) (p : Quiver.Path c.source c.target) :
    coreCalc.Operation c p ≃ Cell p c.edge id id where
  toFun α := α.property ▸ α.val.cell
  invFun α := ⟨⟨p, α⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨q, α⟩, h⟩
    change q = p at h
    cases h
    rfl
  right_inv _ := rfl

/-- Forget the extra scalar, not the endpoints, ordered profile or validity. -/
def forgetScalar : Calc.Hom (coreCalc (X := X)) RelationInterface.containmentCalc where
  map a := ⟨a.profile, a.cell.valid⟩
  profile_map _ := rfl
  map_identity _ := rfl
  map_subst _ _ := rfl

/-- A selected exact/opcartesian marking is NOT imposed on all legitimate cells. -/
def Marked {c : Component (V (X := X))} (a : CoreOp c) : Prop :=
  RelationInterface.evaluate a.profile = c.edge ∧ a.cell.weight = 0

def exactLift : Calc.Hom (RelationInterface.exactCalc (X := X)) coreCalc where
  map a := ⟨a.val, 0, by rw [a.property]; exact fun _ _ h => h⟩
  profile_map _ := rfl
  map_identity _ := rfl
  map_subst a f := by
    apply CoreOp.ext
    · rfl
    change 0 = 0 + Path.sum a.val (fun _ => 0)
    rw [sum_zero]

theorem exactLift_marked {c : Component (V (X := X))} (a : RelationInterface.exactCalc.Op c) :
    Marked (exactLift.map a) := ⟨a.property, rfl⟩

theorem marked_image {c : Component (V (X := X))} (a : CoreOp c) :
    Marked a ↔ ∃ b : RelationInterface.exactCalc.Op c, exactLift.map b = a := by
  constructor
  · rintro ⟨h, hw⟩
    refine ⟨⟨a.profile, h⟩, CoreOp.ext rfl hw.symm⟩
  · rintro ⟨b, rfl⟩
    exact exactLift_marked b

/-- B2's original occurrence-indexed refinement-category functor, not a graph shadow. -/
def refinementComparison (c : Component (V (X := X))) :=
  SemanticRefinement.functor (forgetScalar (X := X)) c

def exactRefinementComparison (c : Component (V (X := X))) :=
  SemanticRefinement.functor (exactLift (X := X)) c


/-- The inverse cartesian bijection is actual substitution into the chosen cell. -/
def restrictionCompose {a b c d e f' : V (X := X)} (p : Quiver.Path a b)
    (H : e ⟶ f') (f : Carrier c → Carrier e) (g : Carrier d → Carrier f')
    (h : Carrier a → Carrier c) (k : Carrier b → Carrier d)
    (β : Cell p (restrict H f g) h k) : Cell p H (f ∘ h) (g ∘ k) :=
  precompose (restrictionCell H f g) h k
    (by intro x y hxy; rw [RelationInterface.evaluate_edge]; exact β.valid x y hxy) β.weight

theorem restriction_factorization {a b c d e f' : V (X := X)} (p : Quiver.Path a b)
    (H : e ⟶ f') (f : Carrier c → Carrier e) (g : Carrier d → Carrier f')
    (h : Carrier a → Carrier c) (k : Carrier b → Carrier d)
    (α : Cell p H (f ∘ h) (g ∘ k)) :
    restrictionCompose p H f g h k (restrictionEquiv p H f g h k α) = α := by
  apply Cell.ext
  exact Nat.zero_add _

theorem restriction_unique {a b c d e f' : V (X := X)} (p : Quiver.Path a b)
    (H : e ⟶ f') (f : Carrier c → Carrier e) (g : Carrier d → Carrier f')
    (h : Carrier a → Carrier c) (k : Carrier b → Carrier d)
    (α : Cell p H (f ∘ h) (g ∘ k))
    (β : Cell p (restrict H f g) h k)
    (hb : restrictionCompose p H f g h k β = α) :
    β = restrictionEquiv p H f g h k α := by
  apply Cell.ext
  have hw := congrArg Cell.weight hb
  change 0 + β.weight = α.weight at hw
  simpa [restrictionEquiv] using hw

theorem evaluate_context_mono {x a b y : V (X := X)}
    (r : Quiver.Path x a) (s : Quiver.Path b y)
    {p q : Quiver.Path a b} (h : RelationInterface.Included (RelationInterface.evaluate p)
      (RelationInterface.evaluate q)) :
    RelationInterface.Included (RelationInterface.evaluate ((r.comp p).comp s))
      (RelationInterface.evaluate ((r.comp q).comp s)) := by
  simp only [RelationInterface.evaluate_comp]
  exact RelationInterface.comp_mono
    (RelationInterface.comp_mono (fun _ _ h => h) h) (fun _ _ h => h)

/-- Actual insertion/substitution of a globular cell into a selected occurrence,
including its scalar; arbitrary prefix, suffix and external boundaries. -/
def contextSubstitute {x a b y d e : V (X := X)}
    (r : Quiver.Path x a) (s : Quiver.Path b y)
    {p : Quiver.Path a b} {H : a ⟶ b} (α : Cell p H id id)
    (K : d ⟶ e) (f : Carrier x → Carrier d) (g : Carrier y → Carrier e)
    (β : Cell ((r.comp H.toPath).comp s) K f g) :
    Cell ((r.comp p).comp s) K f g :=
  ⟨β.weight + α.weight, fun x y hxy => β.valid x y
    (evaluate_context_mono r s (by rw [RelationInterface.evaluate_edge]; exact α.valid) x y hxy)⟩

/-- Universality in every typed surrounding context, not just a weak empty-context property. -/
def ContextualOpcartesian {a b : V (X := X)} {p : Quiver.Path a b} {H : a ⟶ b}
    (α : Cell p H id id) : Prop :=
  ∀ {x y d e : V (X := X)} (r : Quiver.Path x a) (s : Quiver.Path b y)
    (K : d ⟶ e) (f : Carrier x → Carrier d) (g : Carrier y → Carrier e),
    Function.Bijective (contextSubstitute r s α K f g)

/-- The declared exact mark has its real universal meaning in this relational model. -/
theorem marked_contextual {c : Component (V (X := X))} (α : CoreOp c)
    (ha : Marked α) : ContextualOpcartesian α.cell := by
  intro x y d e r s K f g
  have he : RelationInterface.evaluate ((r.comp α.profile).comp s) =
      RelationInterface.evaluate ((r.comp c.edge.toPath).comp s) := by
    simp only [RelationInterface.evaluate_comp, RelationInterface.evaluate_edge]
    rw [ha.1]
  constructor
  · intro β γ hh
    apply Cell.ext
    have hh := congrArg Cell.weight hh
    change β.weight + α.cell.weight = γ.weight + α.cell.weight at hh
    omega
  · intro β
    refine ⟨⟨β.weight, ?_⟩, ?_⟩
    · intro x y hxy
      exact β.valid x y (he.symm ▸ hxy)
    · apply Cell.ext
      change β.weight + α.cell.weight = β.weight
      rw [ha.2, Nat.add_zero]

theorem unit_is_contextual (a : V (X := X)) : ContextualOpcartesian (unitCell a) :=
  marked_contextual (c := ⟨a, a, RelationInterface.diagonal a⟩) ⟨Quiver.Path.nil, unitCell a⟩ ⟨rfl, rfl⟩


/-- The universal property also reflects the mark: a universal cell cannot have
proper relation containment or an unremovable positive scalar. -/
theorem contextual_marked {c : Component (V (X := X))} (α : CoreOp c)
    (hu : ContextualOpcartesian α.cell) : Marked α := by
  let r : Quiver.Path c.source c.source := .nil
  let s : Quiver.Path c.target c.target := .nil
  let β : Cell ((r.comp α.profile).comp s) (RelationInterface.evaluate α.profile) id id :=
    ⟨0, by simp [r, s]⟩
  obtain ⟨γ, hγ⟩ := (hu r s (RelationInterface.evaluate α.profile) id id).2 β
  have hw := congrArg Cell.weight hγ
  change γ.weight + α.cell.weight = 0 at hw
  refine ⟨?_, by omega⟩
  funext x y
  apply propext
  constructor
  · exact α.cell.valid x y
  · intro hxy
    apply γ.valid x y
    change RelationInterface.evaluate c.edge.toPath x y
    rw [RelationInterface.evaluate_edge]
    exact hxy

theorem marked_iff_contextual {c : Component (V (X := X))} (α : CoreOp c) :
    Marked α ↔ ContextualOpcartesian α.cell :=
  ⟨marked_contextual α, contextual_marked α⟩

theorem primitive_not_contextual (a : V (X := X)) :
    ¬ ContextualOpcartesian (nullaryPrimitive a 1) := by
  intro h
  have hh := (contextual_marked (c := ⟨a, a, RelationInterface.diagonal a⟩)
    ⟨Quiver.Path.nil, nullaryPrimitive a 1⟩ h).2
  contradiction

/-- All actual globular equipment witnesses can be declared as original generators.
This is an exhaustive signature, not a claim that arbitrary smaller presentations are full. -/
def equipmentSignature : Signature (V (X := X)) where
  Generator := Σ c : Component (V (X := X)), CoreOp c
  source g := g.1.source
  target g := g.1.target
  input g := g.2.profile
  output g := g.1.edge

def equipmentAssignment : equipmentSignature.Assignment (coreCalc (X := X)) :=
  fun g => ⟨g.2, rfl⟩

def freeCoreMap : Calc.Hom (Tree.freeCalc (equipmentSignature (X := X))) coreCalc :=
  Tree.extend coreCalc equipmentAssignment

/-- Each scalar witness occurs in the image of the actual original free extension. -/
theorem freeCoreMap_surjective (c : Component (V (X := X))) (a : CoreOp c) :
    ∃ t : Tree equipmentSignature c, freeCoreMap.map t = a := by
  refine ⟨Tree.corolla (S := equipmentSignature (X := X)) ⟨c, a⟩, ?_⟩
  exact Tree.interpret_corolla (S := equipmentSignature (X := X)) coreCalc equipmentAssignment ⟨c, a⟩

/-- Checkable preservation class: an equivalence at every interface carrier. -/
abbrev Action (X : I → Type v) := ∀ a : V (X := X), Carrier a ≃ Carrier a

def actRel (A : Action X) {a b : V (X := X)} (H : a ⟶ b) : a ⟶ b :=
  restrict H (A a).symm (A b).symm

def actPath (A : Action X) {a : V (X := X)} :
    {b : V (X := X)} → Quiver.Path a b → Quiver.Path a b
  | _, .nil => .nil
  | _, .cons p H => (actPath A p).cons (actRel A H)

def identityAction : Action X := fun _ => Equiv.refl _
def thenAction (A B : Action X) : Action X := fun a => (A a).trans (B a)

theorem actRel_identity {a b : V (X := X)} (H : a ⟶ b) : actRel identityAction H = H := rfl

theorem actRel_composite (A B : Action X) {a b : V (X := X)} (H : a ⟶ b) :
    actRel B (actRel A H) = actRel (thenAction A B) H := rfl

theorem actPath_identity {a b : V (X := X)} (p : Quiver.Path a b) :
    actPath identityAction p = p := by
  induction p with
  | nil => rfl
  | cons p H ih => simp only [actPath, actRel_identity, ih]

theorem actPath_composite (A B : Action X) {a b : V (X := X)} (p : Quiver.Path a b) :
    actPath B (actPath A p) = actPath (thenAction A B) p := by
  induction p with
  | nil => rfl
  | cons p H ih => simp only [actPath, actRel_composite, ih]

theorem actRel_comp (A : Action X) {a b c : V (X := X)} (H : a ⟶ b) (K : b ⟶ c) :
    RelationInterface.comp (actRel A H) (actRel A K) = actRel A (RelationInterface.comp H K) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hH, hK⟩
    exact ⟨(A b).symm y, hH, hK⟩
  · rintro ⟨y, hH, hK⟩
    refine ⟨A b y, ?_, ?_⟩
    · simpa [actRel, restrict] using hH
    · simpa [actRel, restrict] using hK

theorem actRel_diagonal (A : Action X) (a : V (X := X)) :
    actRel A (RelationInterface.diagonal a) = RelationInterface.diagonal a := by
  funext x y
  apply propext
  exact (A a).symm.injective.eq_iff

/-- Exactness commutes with every arity, zero included; surjectivity is used at
internal witnesses and injectivity at the empty-path diagonal. -/
theorem actPath_evaluate (A : Action X) {a b : V (X := X)} (p : Quiver.Path a b) :
    RelationInterface.evaluate (actPath A p) = actRel A (RelationInterface.evaluate p) := by
  induction p with
  | nil => exact (actRel_diagonal A a).symm
  | cons p H ih =>
    change RelationInterface.comp (RelationInterface.evaluate (actPath A p)) (actRel A H) = _
    rw [ih, actRel_comp]
    rfl

def actCore (A : Action X) {c : Component (V (X := X))} (α : CoreOp c) :
    CoreOp ⟨c.source, c.target, actRel A c.edge⟩ :=
  ⟨actPath A α.profile, α.cell.weight, by
    intro x y h
    rw [actPath_evaluate] at h
    exact α.cell.valid _ _ h⟩

theorem actCore_marked (A : Action X) {c : Component (V (X := X))} (α : CoreOp c)
    (h : Marked α) : Marked (actCore A α) := by
  constructor
  · change RelationInterface.evaluate (actPath A α.profile) = actRel A c.edge
    rw [actPath_evaluate, h.1]
  · exact h.2

theorem actCore_composite (A B : Action X) {c : Component (V (X := X))} (α : CoreOp c) :
    actCore B (actCore A α) = actCore (thenAction A B) α := by
  apply CoreOp.ext
  · exact actPath_composite A B α.profile
  · rfl

theorem actCore_identity {c : Component (V (X := X))} (α : CoreOp c) :
    actCore identityAction α = α := by
  apply CoreOp.ext
  · exact actPath_identity α.profile
  · rfl

theorem actRel_injective (A : Action X) {a b : V (X := X)} :
    Function.Injective (actRel A (a := a) (b := b)) := by
  intro H K h
  funext x y
  have hh := congrFun (congrFun h (A a x)) (A b y)
  simpa [actRel, restrict] using hh

theorem actCore_marked_iff (A : Action X) {c : Component (V (X := X))} (α : CoreOp c) :
    Marked (actCore A α) ↔ Marked α := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    apply actRel_injective A
    exact (actPath_evaluate A α.profile).symm.trans h.1
  · exact actCore_marked A α

/-- The separately stated unit bijection is precisely the actual substitution map. -/
theorem unitContextEquiv_is_substitution {a b c d e : V (X := X)}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (K : d ⟶ e)
    (f : Carrier a → Carrier d) (g : Carrier c → Carrier e)
    (β : Cell ((p.comp (RelationInterface.diagonal b).toPath).comp q) K f g) :
    unitContextEquiv p q K f g β = contextSubstitute p q (unitCell b) K f g β := by
  apply Cell.ext
  exact (Nat.add_zero _).symm

theorem exactLift_injective (c : Component (V (X := X))) :
    Function.Injective (fun a : (RelationInterface.exactCalc (X := X)).Op c => exactLift.map a) := by
  intro a b h
  apply Subtype.ext
  exact congrArg CoreOp.profile h

/-- The exact-to-marked comparison reflects equality of B2's full occurrence tuples. -/
theorem exactRefinement_faithful {c : Component (V (X := X))}
    {a b : (RelationInterface.exactCalc (X := X)).Op c} :
    Function.Injective (SemanticRefinement.mapArrow exactLift (a := a) (b := b)) :=
  SemanticRefinement.mapArrow_injective exactLift exactLift_injective

/-- Parallel scalar witnesses are forgotten ONLY by the declared forgetful morphism. -/
theorem forgetScalar_kernel {c : Component (V (X := X))} (a b : CoreOp c) :
    forgetScalar.map a = forgetScalar.map b ↔ a.profile = b.profile := by
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

#print axioms actCore_marked_iff
#print axioms actCore_identity
#print axioms unitContextEquiv_is_substitution
#print axioms exactLift_injective
#print axioms exactRefinement_faithful
#print axioms forgetScalar_kernel

#print axioms actPath_evaluate
#print axioms actCore_marked
#print axioms actCore_composite

#print axioms restriction_factorization
#print axioms restriction_unique
#print axioms contextSubstitute
#print axioms contextual_marked
#print axioms marked_iff_contextual
#print axioms primitive_not_contextual
#print axioms marked_contextual
#print axioms unit_is_contextual
#print axioms freeCoreMap
#print axioms freeCoreMap_surjective

#print axioms restrictionEquiv
#print axioms restriction_natural
#print axioms restrict_composite
#print axioms evaluate_unit_context
#print axioms unitContextEquiv
#print axioms primitive_substitution_not_surjective
#print axioms coreCalc
#print axioms coreFiberEquiv
#print axioms forgetScalar
#print axioms exactLift
#print axioms marked_image
#print axioms refinementComparison
#print axioms exactRefinementComparison
end E1RelationEquipment
