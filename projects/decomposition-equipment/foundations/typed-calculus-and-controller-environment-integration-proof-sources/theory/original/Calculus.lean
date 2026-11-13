module

public import WitnessedDecompositions.Collections
public import WitnessedDecompositions.PathOccurrences
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe u v w w' w'' w'''
namespace WitnessedDecompositions

namespace Collection
variable {V : Type u} [Quiver.{v} V]

@[simp] theorem profile_occurrenceTransport (C : Collection.{u, v, w} V)
    {c d : Component V} (h : c = d) (a : C.Op c) :
    C.profile (Path.occurrenceTransport C.Op h a) =
      Path.occurrenceTransport (fun e => Quiver.Path e.source e.target) h (C.profile a) := by
  cases h
  rfl

@[simp] theorem profile_expandFamily (C : Collection.{u, v, w} V)
    {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (h : C.Family (Path.expand p q)) (i : Path.Slot p) (j : Path.Slot (q i)) :
    C.profile (Path.expandFamily C.Op p q h i j) =
      Path.expandFamily (fun e => Quiver.Path e.source e.target) p q
        (fun k => C.profile (h k)) i j := by
  unfold Path.expandFamily
  exact C.profile_occurrenceTransport _ _

/-- Equality of profile arrays transports their proof-only fibre wrappers. -/
theorem fiberFamily_mk (C : Collection.{u, v, w} V) {a b : V}
    {p : Quiver.Path a b} (r : C.Family p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (h : ∀ i, C.profile (r i) = q i) :
    (⟨(fun i => C.profile (r i)), (fun i => ⟨r i, rfl⟩)⟩ :
      Σ q : (∀ i : Path.Slot p,
        Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target),
        ∀ i : Path.Slot p, C.Fiber (Path.componentAt p i) (q i)) =
      ⟨q, fun i => ⟨r i, h i⟩⟩ := by
  have hq := funext h
  subst q
  rfl

/-- Families in independently prescribed fibres totalize to precisely ordinary
operation families, without a finiteness or inhabitance hypothesis. -/
def fiberFamilyEquiv (C : Collection.{u, v, w} V) {a b : V}
    (p : Quiver.Path a b) :
    (Σ q : (∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target),
      ∀ i : Path.Slot p, C.Fiber (Path.componentAt p i) (q i)) ≃ C.Family p where
  toFun s := fun i => (s.2 i).val
  invFun f := ⟨(fun i => C.profile (f i)), fun i => ⟨f i, rfl⟩⟩
  left_inv := by
    rintro ⟨q, f⟩
    exact C.fiberFamily_mk (fun i => (f i).val) q (fun i => (f i).property)
  right_inv _ := rfl

/-- Dependent elimination of arbitrary prescribed-profile families via their
total operation family. -/
theorem fiberFamily_induction (C : Collection.{u, v, w} V) {a b : V}
    {p : Quiver.Path a b}
    (P : ∀ q : (∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target),
      (∀ i : Path.Slot p, C.Fiber (Path.componentAt p i) (q i)) → Prop)
    (H : ∀ f : C.Family p, P (fun i => C.profile (f i)) (fun i => ⟨f i, rfl⟩))
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, C.Fiber (Path.componentAt p i) (q i)) : P q f := by
  have h := (C.fiberFamilyEquiv p).left_inv ⟨q, f⟩
  exact (congrArg (fun s => P s.1 s.2) h) ▸ H (fun i => (f i).val)

end Collection

namespace Collection.Hom
variable {V : Type u} [Quiver.{v} V]
variable {C : Collection.{u, v, w} V} {D : Collection.{u, v, w'} V}

@[simp] theorem onFamily_reindex (f : Hom C D) {a b : V}
    {p q : Quiver.Path a b} (h : p = q) (s : C.Family q) :
    f.onFamily (C.reindex h s) = D.reindex h (f.onFamily s) := by
  cases h
  rfl

end Collection.Hom

/-- Operations, their entire profiles, and occurrence-wise substitution data. -/
structure CalcData (V : Type u) [Quiver.{v} V] extends Collection.{u, v, w} V where
  identity : (c : Component V) → Op c
  profile_identity : ∀ c, profile (identity c) = c.edge.toPath
  subst : ∀ {c} (a : Op c), toCollection.Family (profile a) → Op c
  profile_subst : ∀ {c} (a : Op c) (f : toCollection.Family (profile a)),
    profile (subst a f) = toCollection.familyProfile f

namespace CalcData
variable {V : Type u} [Quiver.{v} V]

/-- An independent identity at every position, including repeated equal colors. -/
def identityFamily (M : CalcData.{u, v, w} V) {a b : V} (p : Quiver.Path a b) :
    M.toCollection.Family p := fun i => M.identity (Path.componentAt p i)

@[simp] theorem identityFamily_profile (M : CalcData.{u, v, w} V)
    {a b : V} (p : Quiver.Path a b) :
    M.toCollection.familyProfile (M.identityFamily p) = p := by
  unfold Collection.familyProfile identityFamily
  simp only [M.profile_identity, Path.expand_edges]

/-- Restrict the second layer of a simultaneous substitution to each inserted
operation, after transporting from the actual composite profile. -/
def innerFamily (M : CalcData.{u, v, w} V) {c : Component V}
    (a : M.Op c) (f : M.toCollection.Family (M.profile a))
    (h : M.toCollection.Family (M.profile (M.subst a f)))
    (i : Path.Slot (M.profile a)) : M.toCollection.Family (M.profile (f i)) :=
  Path.expandFamily M.Op (M.profile a) (fun i => M.profile (f i))
    (M.toCollection.reindex (M.profile_subst a f).symm h) i

/-- The composed substitution family, defined using data only, not a law. -/
def composeFamily (M : CalcData.{u, v, w} V) {c : Component V}
    (a : M.Op c) (f : M.toCollection.Family (M.profile a))
    (h : M.toCollection.Family (M.profile (M.subst a f))) :
    M.toCollection.Family (M.profile a) :=
  fun i => M.subst (f i) (M.innerFamily a f h i)

/-- Compose any two profile-indexed families, independently of an outer operation. -/
def composeAt (M : CalcData.{u, v, w} V) {a b : V} {p : Quiver.Path a b}
    (f : M.toCollection.Family p)
    (h : M.toCollection.Family (M.toCollection.familyProfile f)) :
    M.toCollection.Family p := fun i => M.subst (f i)
      (Path.expandFamily M.Op p (fun i => M.profile (f i)) h i)

/-- The canonical profile associator, proved from path expansion and the data's
profile law, with no use of an operation associativity axiom. -/
theorem composeAt_profile (M : CalcData.{u, v, w} V)
    {a b : V} {p : Quiver.Path a b} (f : M.toCollection.Family p)
    (h : M.toCollection.Family (M.toCollection.familyProfile f)) :
    M.toCollection.familyProfile h = M.toCollection.familyProfile (M.composeAt f h) := by
  unfold Collection.familyProfile composeAt
  rw [Path.expand_assoc]
  congr 1
  funext i
  rw [M.profile_subst]
  unfold Collection.familyProfile
  congr 1
  funext j
  exact (M.toCollection.profile_expandFamily p _ h i j).symm

end CalcData

/-- An arbitrary path-profile nonsymmetric multicategory on the fixed quiver.
The laws equate operations, not just their profiles. -/
structure Calc (V : Type u) [Quiver.{v} V] extends CalcData.{u, v, w} V where
  subst_identity : ∀ {c} (a : Op c),
    subst a (toCalcData.identityFamily (profile a)) = a
  identity_subst : ∀ {c} (a : Op c),
    subst (identity c) (toCollection.reindex (profile_identity c)
      (toCollection.singletonFamily a)) = a
  subst_assoc : ∀ {c} (a : Op c) (f : toCollection.Family (profile a))
    (h : toCollection.Family (profile (subst a f))),
    subst (subst a f) h = subst a (toCalcData.composeFamily a f h)

namespace Calc
variable {V : Type u} [Quiver.{v} V]

/-- A genuine operation at the prescribed output and ordered typed profile. -/
abbrev Operation (M : Calc.{u, v, w} V) (c : Component V)
    (p : Quiver.Path c.source c.target) := M.toCollection.Fiber c p

/-- Canonical equality transport on prescribed operation fibres. -/
abbrev transport (M : Calc.{u, v, w} V) {c : Component V}
    {p q : Quiver.Path c.source c.target} (h : p = q) :
    M.Operation c p ≃ M.Operation c q := M.toCollection.transport h

/-- Identity in its prescribed singleton fibre. -/
def identityOperation (M : Calc.{u, v, w} V) (c : Component V) :
    M.Operation c c.edge.toPath := ⟨M.identity c, M.profile_identity c⟩

/-- Substitution by total operations. The input family is indexed by the
advertised profile, never by a presentation-specific datatype. -/
def substituteFamily (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (f : M.toCollection.Family p) : M.Operation c (M.toCollection.familyProfile f) :=
  ⟨M.subst a.val (M.toCollection.reindex a.property f),
    (M.profile_subst _ _).trans (M.toCollection.familyProfile_reindex _ _)⟩

/-- Substitute operations with independently prescribed profiles. The result's
profile is exactly their path expansion, not an existentially supplied profile. -/
def substitute (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i)) :
    M.Operation c (Path.expand p q) :=
  M.transport (by
    unfold Collection.familyProfile
    congr 1
    funext i
    exact (f i).property) (M.substituteFamily a (fun i => (f i).val))

@[simp] theorem substitute_val (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i)) :
    (M.substitute a q f).val =
      M.subst a.val (M.toCollection.reindex a.property (fun i => (f i).val)) := rfl

/-- Right unit in the advertised operation fibre, using canonical profile transport. -/
theorem substituteFamily_identity (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    M.transport (M.toCalcData.identityFamily_profile p)
      (M.substituteFamily a (M.toCalcData.identityFamily p)) = a := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  cases ha
  exact M.subst_identity a

/-- Left unit in the advertised operation fibre, including nullary inserted operations. -/
theorem identityOperation_substituteFamily (M : Calc.{u, v, w} V)
    {c : Component V} (a : M.Op c) :
    M.transport (M.toCollection.singletonFamily_profile a)
      (M.substituteFamily (M.identityOperation c) (M.toCollection.singletonFamily a)) =
        (⟨a, rfl⟩ : M.Operation c (M.profile a)) := by
  apply Subtype.ext
  exact M.identity_subst a

/-- Associativity in prescribed fibres. The transport is the data-only canonical
path associator, not equality of profiles inferred from the operation law. -/
theorem substituteFamily_assoc (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (f : M.toCollection.Family p)
    (h : M.toCollection.Family (M.toCollection.familyProfile f)) :
    M.transport (M.toCalcData.composeAt_profile f h)
      (M.substituteFamily (M.substituteFamily a f) h) =
        M.substituteFamily a (M.toCalcData.composeAt f h) := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  cases ha
  change M.subst (M.subst a f) (M.toCollection.reindex (M.profile_subst a f) h) = _
  rw [M.subst_assoc]
  congr 1
  unfold CalcData.composeFamily CalcData.innerFamily CalcData.composeAt
  rw [Collection.reindex_comp]
  rfl

/-- The right unit stated directly for independently prescribed replacement fibres. -/
theorem substitute_identity (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    M.transport (Path.expand_edges p)
      (M.substitute a (fun i => (Path.componentAt p i).edge.toPath)
        (fun i => M.identityOperation (Path.componentAt p i))) = a := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  cases ha
  exact M.subst_identity a

/-- Assign a prescribed path to the unique occurrence in an identity profile. -/
def singletonProfiles {c : Component V} (p : Quiver.Path c.source c.target) :
    ∀ i : Path.Slot c.edge.toPath,
      Quiver.Path (Path.componentAt c.edge.toPath i).source
        (Path.componentAt c.edge.toPath i).target
  | .inl i => nomatch i
  | .inr () => p

/-- The supplied fibre element at the unique identity occurrence. -/
def singletonOperations (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    ∀ i : Path.Slot c.edge.toPath,
      M.Operation (Path.componentAt c.edge.toPath i) (singletonProfiles p i)
  | .inl i => nomatch i
  | .inr () => a

@[simp] theorem expand_singletonProfiles {c : Component V}
    (p : Quiver.Path c.source c.target) :
    Path.expand c.edge.toPath (singletonProfiles p) = p := Quiver.Path.nil_comp p

/-- Left unit directly in the supplied replacement's prescribed fibre. -/
theorem identityOperation_substitute (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    M.transport (expand_singletonProfiles p)
      (M.substitute (M.identityOperation c) (singletonProfiles p)
        (M.singletonOperations a)) = a := by
  apply Subtype.ext
  change M.subst (M.identity c) (M.toCollection.reindex (M.profile_identity c)
    (fun i => (M.singletonOperations a i).val)) = a.val
  rw [show (fun i => (M.singletonOperations a i).val) =
    M.toCollection.singletonFamily a.val by
      funext i
      rcases i with i | ⟨⟩
      · exact nomatch i
      · rfl]
  exact M.identity_subst a.val

/-- Pull a family of prescribed operations on an expanded profile back to
one inserted operation, preserving its independently supplied local profiles. -/
def expandOperations (M : Calc.{u, v, w} V) {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (r : ∀ k : Path.Slot (Path.expand p q),
      Quiver.Path (Path.componentAt (Path.expand p q) k).source
        (Path.componentAt (Path.expand p q) k).target)
    (h : ∀ k : Path.Slot (Path.expand p q),
      M.Operation (Path.componentAt (Path.expand p q) k) (r k))
    (i : Path.Slot p) (j : Path.Slot (q i)) :
    M.Operation (Path.componentAt (q i) j)
      (Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r i j) := by
  refine ⟨Path.expandFamily M.Op p q (fun k => (h k).val) i j, ?_⟩
  rw [M.toCollection.profile_expandFamily]
  unfold Path.expandFamily
  congr 1
  exact (h _).property

/-- Full two-layer associativity for arbitrary, independently prescribed
replacement profiles. The only output-fibre transport is Path.expand_assoc. -/
theorem substitute_assoc (M : Calc.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i))
    (r : ∀ k : Path.Slot (Path.expand p q),
      Quiver.Path (Path.componentAt (Path.expand p q) k).source
        (Path.componentAt (Path.expand p q) k).target)
    (h : ∀ k : Path.Slot (Path.expand p q),
      M.Operation (Path.componentAt (Path.expand p q) k) (r k)) :
    M.transport (Path.expand_assoc p q r)
      (M.substitute (M.substitute a q f) r h) =
      M.substitute a
        (fun i => Path.expand (q i)
          (Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r i))
        (fun i => M.substitute (f i)
          (Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r i)
          (M.expandOperations p q r h i)) := by
  rcases a with ⟨a, ha⟩
  cases ha
  revert h r f q
  apply M.toCollection.fiberFamily_induction
  intro fs r h
  apply Subtype.ext
  change M.subst (M.subst a fs)
    (M.toCollection.reindex (M.profile_subst a fs) (fun k => (h k).val)) = _
  rw [M.subst_assoc]
  unfold CalcData.composeFamily CalcData.innerFamily
  rw [Collection.reindex_comp]
  rfl

/-- Strict morphisms preserve the complete profile, identities, and every
occurrence-wise substitution. Operation universes may differ. -/
structure Hom (M : Calc.{u, v, w} V) (N : Calc.{u, v, w'} V)
    extends Collection.Hom M.toCollection N.toCollection where
  map_identity : ∀ c, map (M.identity c) = N.identity c
  map_subst : ∀ {c} (a : M.Op c) (f : M.toCollection.Family (M.profile a)),
    map (M.subst a f) = N.subst (map a)
      (N.toCollection.reindex (profile_map a) (toHom.onFamily f))

namespace Hom
variable {M : Calc.{u, v, w} V} {N : Calc.{u, v, w'} V}
  {P : Calc.{u, v, w''} V}

@[ext] theorem ext {f g : Hom M N}
    (h : ∀ c (a : M.Op c), f.map a = g.map a) : f = g := by
  cases f with
  | mk f fi fs =>
    cases g with
    | mk g gi gs =>
      have : f = g := Collection.Hom.ext h
      cases this
      rfl

/-- Identity strict calculus morphism. -/
def id (M : Calc.{u, v, w} V) : Hom M M where
  toHom := Collection.Hom.id M.toCollection
  map_identity _ := rfl
  map_subst _ _ := rfl

/-- Composition of strict calculus morphisms, with the canonical full-profile
transports composed explicitly. -/
def comp (f : Hom M N) (g : Hom N P) : Hom M P where
  toHom := f.toHom.comp g.toHom
  map_identity c := by
    change g.map (f.map (M.identity c)) = _
    rw [f.map_identity, g.map_identity]
  map_subst a s := by
    change g.map (f.map (M.subst a s)) = _
    rw [f.map_subst, g.map_subst]
    congr 1
    rw [Collection.Hom.onFamily_reindex, Collection.reindex_comp]
    rfl

@[simp] theorem id_comp (f : Hom M N) : (id M).comp f = f := by
  apply ext
  intros
  rfl

@[simp] theorem comp_id (f : Hom M N) : f.comp (id N) = f := by
  apply ext
  intros
  rfl

theorem comp_assoc {Q : Calc.{u, v, w'''} V}
    (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply ext
  intros
  rfl

/-- The induced map on every prescribed operation fibre. -/
abbrev onOperation (f : Hom M N) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    N.Operation c p := f.toHom.onFiber a

@[simp] theorem onOperation_identity (f : Hom M N) (c : Component V) :
    f.onOperation (M.identityOperation c) = N.identityOperation c := by
  apply Subtype.ext
  exact f.map_identity c

/-- Strict morphisms preserve every prescribed-profile substitution literally in
its common output fibre. -/
theorem onOperation_substitute (f : Hom M N) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (s : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i)) :
    f.onOperation (M.substitute a q s) =
      N.substitute (f.onOperation a) q (fun i => f.onOperation (s i)) := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  cases ha
  exact f.map_subst a (fun i => (s i).val)

end Hom

/-- Arbitrary path-profile calculi and strict maps form a category at each
operation universe; the Hom API itself also permits distinct universes. -/
instance : CategoryTheory.Category (Calc.{u, v, w} V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end Calc
end WitnessedDecompositions
