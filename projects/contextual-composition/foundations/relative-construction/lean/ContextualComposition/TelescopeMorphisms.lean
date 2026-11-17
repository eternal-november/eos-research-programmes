module
public import ContextualComposition.FiniteTelescope
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Types.Basic
@[expose] public section
namespace ContextualComposition.FiniteTelescope
open CategoryTheory
universe u v w
variable {B : Type u} {G : Span.{u,v} B} [∀ a b, Category.{w} (G a b)]

/-- A morphism preserves the state sequence and supplies an actual arrow at each grade. -/
inductive ChainHom : {a b : B} → Chain G a b → Chain G a b → Type (max u v w)
  | nil (a : B) : ChainHom (.nil a) (.nil a)
  | cons {a b c : B} {g h : G a b} {p q : Chain G b c}
      (f : g ⟶ h) (r : ChainHom p q) : ChainHom (.cons g p) (.cons h q)

namespace ChainHom
def ident {a b} (p : Chain G a b) : ChainHom p p :=
  match p with
  | .nil a => .nil a
  | .cons g p => .cons (𝟙 g) (ident p)

def compose {a b} {p q r : Chain G a b} (f : ChainHom p q) (g : ChainHom q r) : ChainHom p r :=
  match f, g with
  | .nil _, .nil i => .nil i
  | .cons f fs, .cons g gs => .cons (f ≫ g) (compose fs gs)

theorem ident_compose {a b} {p q : Chain G a b} (f : ChainHom p q) : compose (ident p) f = f := by
  induction f with
  | nil => rfl
  | cons f fs ih => simp [ident,compose,ih]

theorem compose_ident {a b} {p q : Chain G a b} (f : ChainHom p q) : compose f (ident q) = f := by
  induction f with
  | nil => rfl
  | cons f fs ih => simp [ident,compose,ih]

theorem compose_assoc {a b} {p q r s : Chain G a b}
    (f : ChainHom p q) (g : ChainHom q r) (h : ChainHom r s) :
    compose (compose f g) h = compose f (compose g h) := by
  induction f with
  | nil => cases g; cases h; rfl
  | cons f fs ih => cases g with
    | cons g gs => cases h with
      | cons h hs => simp [compose, Category.assoc, ih]

instance chainCategory (a b : B) : Category (Chain G a b) where
  Hom := ChainHom
  id := ident
  comp := compose
  id_comp := ident_compose
  comp_id := compose_ident
  assoc := compose_assoc

def singletonArrow {a b} {g h : G a b} (f : g ⟶ h) :
    ChainHom (singleton g) (singleton h) := .cons f (.nil b)

def singletonFunctor (a b : B) : G a b ⥤ Chain G a b where
  obj := singleton
  map := singletonArrow
  map_id _ := rfl
  map_comp _ _ := rfl

def firstArrow {a b c} {g h : G a b} {p q : Chain G b c}
    (f : ChainHom (.cons g p) (.cons h q)) : g ⟶ h :=
  match f with
  | .cons k _ => k

def singletonHomEquiv {a b} (g h : G a b) :
    (g ⟶ h) ≃ (singleton g ⟶ singleton h) where
  toFun := singletonArrow
  invFun := firstArrow
  left_inv _ := rfl
  right_inv f := by
    change ChainHom (singleton g) (singleton h) at f
    cases f with
    | cons k r => cases r; rfl

def appendArrow {a b} {p q : Chain G a b} (f : ChainHom p q) :
    ∀ {c} {r s : Chain G b c}, ChainHom r s → ChainHom (append p r) (append q s) :=
  match a, b, p, q, f with
  | _, _, _, _, .nil _ => fun h => h
  | _, _, _, _, .cons k t => fun h => .cons k (appendArrow t h)

theorem appendArrow_ident {a b c} (p : Chain G a b) (q : Chain G b c) :
    appendArrow (ident p) (ident q) = ident (append p q) := by
  induction p with
  | nil => rfl
  | cons g r ih => exact congrArg (ChainHom.cons (𝟙 g)) (ih q)

/-- Concatenation preserves simultaneous vertical composites, with the two input arrows independent. -/
theorem appendArrow_compose {a b c} {p q r : Chain G a b} {s t u : Chain G b c}
    (f : ChainHom p q) (g : ChainHom q r) (h : ChainHom s t) (k : ChainHom t u) :
    appendArrow (compose f g) (compose h k) = compose (appendArrow f h) (appendArrow g k) := by
  induction f with
  | nil => cases g; rfl
  | cons f fs ih => cases g with
    | cons g gs => exact congrArg (ChainHom.cons (f ≫ g)) (ih gs h k)

/-- Nested chains use the chain categories themselves as grade categories. -/
def flattenArrow {a b} {p q : Chain (Chain G) a b} (f : ChainHom p q) :
    ChainHom (flatten p) (flatten q) :=
  match f with
  | .nil i => .nil i
  | .cons k t => appendArrow k (flattenArrow t)

theorem flattenArrow_ident {a b} (p : Chain (Chain G) a b) :
    flattenArrow (ident p) = ident (flatten p) := by
  induction p with
  | nil => rfl
  | cons g r ih =>
    change appendArrow (ident g) (flattenArrow (ident r)) = _
    rw [ih, appendArrow_ident]
    rfl

theorem flattenArrow_compose {a b} {p q r : Chain (Chain G) a b}
    (f : ChainHom p q) (g : ChainHom q r) :
    flattenArrow (compose f g) = compose (flattenArrow f) (flattenArrow g) := by
  induction f with
  | nil => cases g; rfl
  | cons f fs ih => cases g with
    | cons g gs =>
      change appendArrow (compose f g) (flattenArrow (compose fs gs)) = _
      rw [ih, appendArrow_compose]
      rfl

def flattenFunctor (a b : B) : Chain (Chain G) a b ⥤ Chain G a b where
  obj := flatten
  map := flattenArrow
  map_id := flattenArrow_ident
  map_comp := flattenArrow_compose

theorem length_preserved {a b} {p q : Chain G a b} (f : ChainHom p q) : length p = length q := by
  induction f with
  | nil => rfl
  | cons f fs ih => exact congrArg Nat.succ ih

theorem singleton_reflects_iso {a b} {g h : G a b} (f : g ⟶ h)
    [inst : IsIso ((singletonFunctor (G := G) a b).map f)] : IsIso f := by
  let F := singletonFunctor (G := G) a b
  obtain ⟨l,hl,hr⟩ := inst.out
  let k := (singletonHomEquiv h g).symm l
  have hk : F.map k = l := (singletonHomEquiv h g).apply_symm_apply l
  refine ⟨⟨k, ?_, ?_⟩⟩
  · apply (singletonHomEquiv g g).injective
    change F.map (f ≫ k) = F.map (𝟙 g)
    rw [F.map_comp, hk, F.map_id]
    exact hl
  · apply (singletonHomEquiv h h).injective
    change F.map (k ≫ f) = F.map (𝟙 h)
    rw [F.map_comp, hk, F.map_id]
    exact hr

private theorem cons_heq {a b c} {g h : G a b} (k : g ⟶ h)
    {p q p' q' : Chain G b c} {r : ChainHom p q} {t : ChainHom p' q'}
    (hp : p = p') (hq : q = q') (ht : HEq r t) : HEq (cons k r) (cons k t) := by
  subst p'; subst q'; cases ht; rfl

theorem appendArrow_nil_right {a b} {p q : Chain G a b} (f : ChainHom p q) :
    HEq (appendArrow f (.nil b)) f := by
  induction f with
  | nil => rfl
  | cons k r ih => exact cons_heq k (append_nil _) (append_nil _) ih


theorem flattenArrow_singleton {a b} {p q : Chain G a b} (f : ChainHom p q) :
    HEq (flattenArrow (singletonArrow (G := Chain G) f)) f :=
  appendArrow_nil_right f

/-- Insert a length-one block around every grade arrow, retaining its endpoints. -/
def blockSingleton {a b} {p q : Chain G a b} (f : ChainHom p q) :
    ChainHom (map (@singleton B G) p) (map (@singleton B G) q) :=
  match f with
  | .nil i => .nil i
  | .cons k t => .cons (singletonArrow k) (blockSingleton t)

theorem flattenArrow_blockSingleton {a b} {p q : Chain G a b} (f : ChainHom p q) :
    HEq (flattenArrow (blockSingleton f)) f := by
  induction f with
  | nil => rfl
  | cons k r ih => exact cons_heq k (flatten_map_singleton _) (flatten_map_singleton _) ih

/-- Homogeneous decoding of dependent arrow equality using the declared object equalities. -/
theorem transport_eq_of_heq {a b} {p q p' q' : Chain G a b} (f : ChainHom p q) (g : ChainHom p' q')
    (h : HEq f g) (hp : p = p') (hq : q = q') : hp ▸ hq ▸ f = g := by
  subst p'; subst q'; exact eq_of_heq h

theorem flatten_singleton_arrow_eq {a b} {p q : Chain G a b} (f : ChainHom p q) :
    (flatten_singleton p) ▸ (flatten_singleton q) ▸
      flattenArrow (singletonArrow (G := Chain G) f) = f :=
  transport_eq_of_heq _ _ (flattenArrow_singleton f) _ _

theorem flatten_blockSingleton_arrow_eq {a b} {p q : Chain G a b} (f : ChainHom p q) :
    (flatten_map_singleton p) ▸ (flatten_map_singleton q) ▸ flattenArrow (blockSingleton f) = f :=
  transport_eq_of_heq _ _ (flattenArrow_blockSingleton f) _ _


theorem appendArrow_assoc {a b c d} {p q : Chain G a b} {r s : Chain G b c} {t u : Chain G c d}
    (f : ChainHom p q) (g : ChainHom r s) (h : ChainHom t u) :
    HEq (appendArrow (appendArrow f g) h) (appendArrow f (appendArrow g h)) := by
  induction f with
  | nil => rfl
  | cons k r ih => exact cons_heq k (append_assoc _ _ _) (append_assoc _ _ _) (ih g)

private theorem append_congr_right {a b c} {p q : Chain G a b} (f : ChainHom p q)
    {r s r' s' : Chain G b c} {g : ChainHom r s} {g' : ChainHom r' s'}
    (hr : r = r') (hs : s = s') (h : HEq g g') : HEq (appendArrow f g) (appendArrow f g') := by
  subst r'; subst s'; cases h; rfl

theorem flattenArrow_append {a b c} {p q : Chain (Chain G) a b} {r s : Chain (Chain G) b c}
    (f : ChainHom p q) (g : ChainHom r s) :
    HEq (flattenArrow (appendArrow f g)) (appendArrow (flattenArrow f) (flattenArrow g)) := by
  induction f with
  | nil => rfl
  | cons k r ih =>
    exact (append_congr_right k (flatten_append _ _) (flatten_append _ _) (ih g)).trans
      (appendArrow_assoc k _ (flattenArrow g)).symm

/-- Apply flattening to each block rather than first flattening the outer chain. -/
def blockFlatten {a b} {p q : Chain (Chain (Chain G)) a b} (f : ChainHom p q) :
    ChainHom (map (@flatten B G) p) (map (@flatten B G) q) :=
  match f with
  | .nil i => .nil i
  | .cons k t => .cons (flattenArrow k) (blockFlatten t)

theorem flattenArrow_assoc {a b} {p q : Chain (Chain (Chain G)) a b} (f : ChainHom p q) :
    HEq (flattenArrow (flattenArrow f)) (flattenArrow (blockFlatten f)) := by
  induction f with
  | nil => rfl
  | cons k r ih =>
    exact (flattenArrow_append k (flattenArrow r)).trans
      (append_congr_right (flattenArrow k) (flatten_assoc _) (flatten_assoc _) ih)

theorem flatten_assoc_arrow_eq {a b} {p q : Chain (Chain (Chain G)) a b} (f : ChainHom p q) :
    (flatten_assoc p) ▸ (flatten_assoc q) ▸ flattenArrow (flattenArrow f) =
      flattenArrow (blockFlatten f) :=
  transport_eq_of_heq _ _ (flattenArrow_assoc f) _ _


section Witness
/-- One-state example solely to probe the arrow interface: grades themselves are types. -/
def typeSpan : Span Unit := fun _ _ => Type
instance typeSpanCategory (a b : Unit) : Category (typeSpan a b) :=
  inferInstanceAs (Category (Type))

/-- The empty-to-unit function supplies a chain arrow whose reverse hom is empty. -/
theorem empty_unit_no_reverse :
    IsEmpty ((singleton (G := typeSpan) (a := ()) (b := ()) Unit) ⟶ singleton Empty) :=
  ⟨fun r => Empty.elim (TypeCat.homEquiv ((singletonHomEquiv (G := typeSpan) Unit Empty).symm r) ())⟩

def empty_unit_arrow :
    singleton (G := typeSpan) (a := ()) (b := ()) Empty ⟶ singleton Unit :=
  singletonArrow (G := typeSpan) (g := Empty) (h := Unit) (TypeCat.ofHom (fun x : Empty => nomatch x))

/-- Two maps with identical source and target grades are not identified as one chain map. -/
theorem parallel_native_maps_distinct :
    singletonArrow (G := typeSpan) (a := ()) (b := ()) (g := Bool) (h := Bool) (TypeCat.ofHom (fun x : Bool => x)) ≠
      singletonArrow (G := typeSpan) (g := Bool) (h := Bool) (TypeCat.ofHom (fun _ : Bool => false)) := by
  intro h
  have h' := (singletonHomEquiv (G := typeSpan) (a := ()) (b := ()) Bool Bool).injective h
  have h'' := congrArg (fun f : Bool ⟶ Bool => TypeCat.homEquiv f true) h'
  cases h''
end Witness
end ChainHom
end ContextualComposition.FiniteTelescope
