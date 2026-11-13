module

public import WitnessedDecompositions.Core
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Profiled collections and their strict maps

These are arbitrary operation spaces over the fixed interface/component base,
not algebras with an arbitrary value at a component leaf. A prescribed profile
always has a genuine fibre. The total-space convention is explicitly equivalent
to giving a type separately for every profile.
-/

@[expose] public section

universe u v w w' w''

namespace WitnessedDecompositions

/-- Equality induces a constructive equivalence; no choice of representative is made. -/
def equalityEquiv {α β : Sort w} (h : α = β) : α ≃ β := by
  cases h
  exact Equiv.refl α

namespace Component

variable {V : Type u} [Quiver.{v} V]

/-- Transport a component-indexed value without forgetting either endpoint. -/
def transport {F : Component V → Sort w} {c d : Component V}
    (h : c = d) (x : F c) : F d := h ▸ x

@[simp] theorem transport_rfl {F : Component V → Sort w} {c : Component V}
    (x : F c) : transport rfl x = x := rfl

@[simp] theorem transport_trans {F : Component V → Sort w} {a b c : Component V}
    (h : a = b) (k : b = c) (x : F a) :
    transport k (transport h x) = transport (h.trans k) x := by
  cases h
  cases k
  rfl

@[simp] theorem transport_symm {F : Component V → Sort w} {c d : Component V}
    (h : c = d) (x : F c) : transport h.symm (transport h x) = x := by
  cases h
  rfl

end Component

/-- A collection of operations with their entire ordered typed profile retained. -/
structure Collection (V : Type u) [Quiver.{v} V] where
  Op : Component V → Type w
  profile : ∀ {c}, Op c → Quiver.Path c.source c.target

namespace Collection

variable {V : Type u} [Quiver.{v} V]

/-- The operation fibre at a fixed ordered profile and output. -/
def Fiber (C : Collection.{u, v, w} V) (c : Component V)
    (p : Quiver.Path c.source c.target) := {a : C.Op c // C.profile a = p}

/-- Independent operations at the positions of an ordered profile. -/
def Family (C : Collection.{u, v, w} V) {a b : V} (p : Quiver.Path a b) :=
  ∀ i : Path.Slot p, C.Op (Path.componentAt p i)

/-- The profile obtained by the specified independent replacements. -/
def familyProfile (C : Collection.{u, v, w} V) {a b : V}
    {p : Quiver.Path a b} (f : C.Family p) : Quiver.Path a b :=
  Path.expand p (fun i => C.profile (f i))

/-- Equality transport in a prescribed operation fibre. -/
def transport (C : Collection.{u, v, w} V) {c : Component V}
    {p q : Quiver.Path c.source c.target} (h : p = q) : C.Fiber c p ≃ C.Fiber c q where
  toFun a := ⟨a.val, a.property.trans h⟩
  invFun a := ⟨a.val, a.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem transport_val (C : Collection.{u, v, w} V) {c : Component V}
    {p q : Quiver.Path c.source c.target} (h : p = q) (a : C.Fiber c p) :
    (C.transport h a).val = a.val := rfl

@[simp] theorem transport_refl (C : Collection.{u, v, w} V) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : C.Fiber c p) : C.transport rfl a = a := rfl

@[simp] theorem transport_comp (C : Collection.{u, v, w} V) {c : Component V}
    {p q r : Quiver.Path c.source c.target} (h : p = q) (k : q = r) (a : C.Fiber c p) :
    C.transport k (C.transport h a) = C.transport (h.trans k) a := rfl

/-- Reindex a substitution family along equality of the *whole* typed profile. -/
def reindex (C : Collection.{u, v, w} V) {a b : V}
    {p q : Quiver.Path a b} (h : p = q) (f : C.Family q) : C.Family p := h ▸ f

@[simp] theorem reindex_refl (C : Collection.{u, v, w} V) {a b : V}
    {p : Quiver.Path a b} (f : C.Family p) : C.reindex rfl f = f := rfl

@[simp] theorem reindex_comp (C : Collection.{u, v, w} V) {a b : V}
    {p q r : Quiver.Path a b} (h : p = q) (k : q = r) (f : C.Family r) :
    C.reindex h (C.reindex k f) = C.reindex (h.trans k) f := by
  cases h
  cases k
  rfl

@[simp] theorem familyProfile_reindex (C : Collection.{u, v, w} V) {a b : V}
    {p q : Quiver.Path a b} (h : p = q) (f : C.Family q) :
    C.familyProfile (C.reindex h f) = C.familyProfile f := by
  cases h
  rfl

/-- One replacement at the sole position of a singleton identity profile. -/
def singletonFamily (C : Collection.{u, v, w} V) {c : Component V} (a : C.Op c) :
    C.Family c.edge.toPath
  | .inl i => nomatch i
  | .inr () => a

@[simp] theorem singletonFamily_profile (C : Collection.{u, v, w} V)
    {c : Component V} (a : C.Op c) : C.familyProfile (C.singletonFamily a) = C.profile a := by
  exact Quiver.Path.nil_comp _

/-- Start with completely arbitrary fibre types; form their disjoint total space. -/
def totalize (F : ∀ c : Component V, Quiver.Path c.source c.target → Type w) :
    Collection.{u, v, max u v w} V where
  Op c := (p : Quiver.Path c.source c.target) × F c p
  profile a := a.1

/-- Taking fibres after totalization recovers every original operation type. -/
def fiberTotalizeEquiv (F : ∀ c : Component V, Quiver.Path c.source c.target → Type w)
    (c : Component V) (p : Quiver.Path c.source c.target) :
    (totalize F).Fiber c p ≃ F c p where
  toFun a := a.property ▸ a.val.2
  invFun a := ⟨⟨p, a⟩, rfl⟩
  left_inv a := by
    rcases a with ⟨⟨q, a⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- Totalizing the genuine fibres of a collection recovers its total operation space. -/
def totalizeFiberEquiv (C : Collection.{u, v, w} V) (c : Component V) :
    (totalize C.Fiber).Op c ≃ C.Op c where
  toFun a := a.2.val
  invFun a := ⟨C.profile a, ⟨a, rfl⟩⟩
  left_inv a := by
    rcases a with ⟨p, a, h⟩
    cases h
    rfl
  right_inv _ := rfl

@[simp] theorem totalizeFiberEquiv_profile (C : Collection.{u, v, w} V)
    (c : Component V) (a : (totalize C.Fiber).Op c) :
    C.profile (C.totalizeFiberEquiv c a) = (totalize C.Fiber).profile a := a.2.property

/-- Strict maps preserve the complete ordered profile, not merely its length. -/
structure Hom (C : Collection.{u, v, w} V) (D : Collection.{u, v, w'} V) where
  map : ∀ {c}, C.Op c → D.Op c
  profile_map : ∀ {c} (a : C.Op c), D.profile (map a) = C.profile a

namespace Hom

variable {C : Collection.{u, v, w} V} {D : Collection.{u, v, w'} V}
    {E : Collection.{u, v, w''} V}

@[ext] theorem ext {f g : Hom C D} (h : ∀ c (a : C.Op c), f.map a = g.map a) : f = g := by
  cases f with
  | mk fm fp =>
    cases g with
    | mk gm gp =>
      have : @fm = @gm := by
        funext c a
        exact h c a
      cases this
      rfl

/-- Identity strict collection map. -/
def id (C : Collection.{u, v, w} V) : Hom C C where
  map a := a
  profile_map _ := rfl

/-- Composite of strict maps; no profile is changed. -/
def comp (f : Hom C D) (g : Hom D E) : Hom C E where
  map a := g.map (f.map a)
  profile_map a := (g.profile_map (f.map a)).trans (f.profile_map a)

@[simp] theorem id_comp (f : Hom C D) : (id C).comp f = f := rfl
@[simp] theorem comp_id (f : Hom C D) : f.comp (id D) = f := rfl

theorem comp_assoc {F : Collection V} (f : Hom C D) (g : Hom D E) (h : Hom E F) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

/-- Strict maps act on prescribed operation fibres. -/
def onFiber (f : Hom C D) {c : Component V} {p : Quiver.Path c.source c.target}
    (a : C.Fiber c p) : D.Fiber c p :=
  ⟨f.map a.val, (f.profile_map a.val).trans a.property⟩

/-- Strict maps act independently at every profile position. -/
def onFamily (f : Hom C D) {a b : V} {p : Quiver.Path a b} (s : C.Family p) :
    D.Family p := fun i => f.map (s i)

@[simp] theorem familyProfile_onFamily (f : Hom C D) {a b : V}
    {p : Quiver.Path a b} (s : C.Family p) :
    D.familyProfile (f.onFamily s) = C.familyProfile s := by
  unfold familyProfile onFamily
  congr 1
  funext i
  exact f.profile_map (s i)

end Hom

/-- The category of arbitrary profiled operation collections over the fixed base. -/
instance : CategoryTheory.Category (Collection.{u, v, w} V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end Collection

namespace Tree

variable {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V)

/-- The free tree operation collection has exactly the seed's operation fibres. -/
def collection : Collection V where
  Op := Tree S
  profile := frontier

theorem collection_fiber (c : Component V) (p : Quiver.Path c.source c.target) :
    (collection S).Fiber c p = Operation (S := S) c p := rfl

end Tree

end WitnessedDecompositions
