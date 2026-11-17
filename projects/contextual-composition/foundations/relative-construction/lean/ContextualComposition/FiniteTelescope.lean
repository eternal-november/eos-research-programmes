module
public import Mathlib.CategoryTheory.Category.Basic
@[expose] public section
namespace ContextualComposition.FiniteTelescope
universe u v w t
variable {B : Type u}
-- A discrete span over a discrete base, presented by its two endpoint fibres.
abbrev Span (B : Type u) := B → B → Type v

/-- A finite dependent telescope. Each tail starts at the endpoint of its actual head grade. -/
inductive Chain (G : Span.{u,v} B) : B → B → Type (max u v)
  | nil (a : B) : Chain G a a
  | cons {a b c : B} (g : G a b) (p : Chain G b c) : Chain G a c

variable {G : Span.{u,v} B}
def singleton {a b : B} (g : G a b) : Chain G a b := .cons g (.nil b)

def append {a b c : B} (p : Chain G a b) (q : Chain G b c) : Chain G a c :=
  match p with
  | .nil _ => q
  | .cons g r => .cons g (append r q)

theorem append_nil {a b : B} (p : Chain G a b) : append p (.nil b) = p := by
  induction p with
  | nil => rfl
  | cons g r ih => exact congrArg (Chain.cons g) ih

theorem append_assoc {a b c d : B} (p : Chain G a b) (q : Chain G b c) (r : Chain G c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil => rfl
  | cons g s ih => exact congrArg (Chain.cons g) (ih q)

def map {H : Span.{u,w} B} (f : ∀ {a b}, G a b → H a b) {a b} (p : Chain G a b) : Chain H a b :=
  match p with
  | .nil i => .nil i
  | .cons g r => .cons (f g) (map f r)

/-- Telescope multiplication forgets boundaries between blocks, not the grades in the blocks. -/
def flatten {a b : B} (p : Chain (Chain G) a b) : Chain G a b :=
  match p with
  | .nil i => .nil i
  | .cons q r => append q (flatten r)

theorem flatten_singleton {a b : B} (p : Chain G a b) : flatten (singleton p) = p :=
  append_nil p

theorem flatten_map_singleton {a b : B} (p : Chain G a b) :
    flatten (map (@singleton B G) p) = p := by
  induction p with
  | nil => rfl
  | cons g r ih => exact congrArg (Chain.cons g) ih

theorem flatten_append {a b c : B} (p : Chain (Chain G) a b) (q : Chain (Chain G) b c) :
    flatten (append p q) = append (flatten p) (flatten q) := by
  induction p with
  | nil => rfl
  | cons g r ih => exact (congrArg (append g) (ih q)).trans (append_assoc g _ _).symm

theorem flatten_assoc {a b : B} (p : Chain (Chain (Chain G)) a b) :
    flatten (flatten p) = flatten (map (@flatten B G) p) := by
  induction p with
  | nil => rfl
  | cons g r ih =>
    change flatten (append g (flatten r)) = append (flatten g) _
    rw [flatten_append, ih]

def length {a b} (p : Chain G a b) : Nat :=
  match p with
  | .nil _ => 0
  | .cons _ r => length r + 1

theorem singleton_length {a b : B} (g : G a b) : length (singleton g) = 1 := rfl

/-- One summand for each admissible next endpoint and each actual grade, with a dependent payload. -/
def Step (G : Span.{u,v} B) (X : B → Type w) (a : B) := Σ b, G a b × X b

-- Fixed output universe allows all successive iterates even when base, grade and values differ in size.
def Iter (G : Span.{u,v} B) (X : B → Type (max u v w)) : Nat → B → Type (max u v w)
  | 0 => X
  | n+1 => Step G (Iter G X n)

def Value (G : Span.{u,v} B) (X : B → Type (max u v w)) (a : B) :=
  Σ b, Chain G a b × X b

/-- Unit at the value family for the free endofunctor monad; no grade is inserted. -/
def emptyValue {X : B → Type (max u v w)} {a : B} (x : X a) : Value G X a :=
  ⟨a, .nil a, x⟩

def pack {X : B → Type (max u v w)} {a b : B} (p : Chain G a b) (x : X b) :
    Σ n, Iter G X n a :=
  match p with
  | .nil _ => ⟨0,x⟩
  | .cons (b := j) g r =>
    let t := pack r x
    ⟨t.1+1, j, g, t.2⟩

def unpack {X : B → Type (max u v w)} {a : B} (n : Nat) (z : Iter G X n a) : Value G X a :=
  match n with
  | 0 => emptyValue z
  | n+1 =>
    let t := unpack n z.2.2
    ⟨t.1, .cons z.2.1 t.2.1, t.2.2⟩

theorem unpack_pack {X : B → Type (max u v w)} {a b : B} (p : Chain G a b) (x : X b) :
    unpack (pack p x).1 (pack p x).2 = (⟨b,p,x⟩ : Value G X a) := by
  induction p with
  | nil => rfl
  | @cons i j k g r ih =>
    exact congrArg (fun t : Value G X j => (⟨t.1, Chain.cons g t.2.1, t.2.2⟩ : Value G X i)) (ih x)

theorem pack_unpack {X : B → Type (max u v w)} {a : B} (n : Nat) (z : Iter G X n a) :
    pack (unpack n z).2.1 (unpack n z).2.2 = ⟨n,z⟩ := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rcases z with ⟨b,g,y⟩
    exact congrArg (fun t : Σ k, Iter G X k b =>
      (⟨t.1+1, b, g, t.2⟩ : Σ k, Iter G X k a)) (ih y)

def extensionEquiv (G : Span.{u,v} B) (X : B → Type (max u v w)) (a : B) :
    Value G X a ≃ Σ n, Iter G X n a where
  toFun z := pack z.2.1 z.2.2
  invFun z := unpack z.1 z.2
  left_inv z := unpack_pack z.2.1 z.2.2
  right_inv z := pack_unpack z.1 z.2

theorem emptyValue_summand {X : B → Type (max u v w)} {a : B} (x : X a) :
    extensionEquiv G X a (emptyValue x) = ⟨0,x⟩ := rfl

/-- A context-indexed grade family with specified extension gives a directed span.
A grade with wrong successor cannot inhabit the requisite endpoint fibre. -/
def fromExtension (Grade : B → Type v) (extend : ∀ a, Grade a → B) : Span B :=
  fun a b => {g : Grade a // extend a g = b}

theorem map_id {a b : B} (p : Chain G a b) : map (fun g => g) p = p := by
  induction p with
  | nil => rfl
  | cons g r ih => exact congrArg (Chain.cons g) ih

theorem map_comp {H : Span.{u,w} B} {I : Span.{u,t} B}
    (f : ∀ {a b}, G a b → H a b) (g : ∀ {a b}, H a b → I a b) {a b} (p : Chain G a b) :
    map g (map f p) = map (fun k => g (f k)) p := by
  induction p with
  | nil => rfl
  | cons e r ih => exact congrArg (Chain.cons (g (f e))) ih

theorem map_append {H : Span.{u,w} B} (f : ∀ {a b}, G a b → H a b)
    {a b c} (p : Chain G a b) (q : Chain G b c) :
    map f (append p q) = append (map f p) (map f q) := by
  induction p with
  | nil => rfl
  | cons e r ih => exact congrArg (Chain.cons (f e)) (ih q)

theorem flatten_natural {H : Span.{u,w} B} (f : ∀ {a b}, G a b → H a b)
    {a b} (p : Chain (Chain G) a b) : map f (flatten p) = flatten (map (map f) p) := by
  induction p with
  | nil => rfl
  | cons q r ih => exact (map_append f q (flatten r)).trans (congrArg (append (map f q)) ih)

def valueMap {X Y : B → Type (max u v w)} (f : ∀ b, X b → Y b) {a} (z : Value G X a) :
    Value G Y a := ⟨z.1,z.2.1,f z.1 z.2.2⟩

def iterMap {X Y : B → Type (max u v w)} (f : ∀ b, X b → Y b) (n : Nat) {a}
    (z : Iter G X n a) : Iter G Y n a :=
  match n with
  | 0 => f a z
  | n+1 => ⟨z.1,z.2.1,iterMap f n z.2.2⟩

/-- Naturality of the coproduct comparison on all maps of payload families. -/
theorem extension_natural {X Y : B → Type (max u v w)} (f : ∀ b, X b → Y b)
    {a} (z : Value G X a) :
    extensionEquiv G Y a (valueMap f z) =
      (let t := extensionEquiv G X a z; ⟨t.1,iterMap f t.1 t.2⟩) := by
  rcases z with ⟨b,p,x⟩
  induction p with
  | nil => rfl
  | @cons i j k g r ih =>
    exact congrArg (fun t : Σ n, Iter G Y n j =>
      (⟨t.1+1,j,g,t.2⟩ : Σ n, Iter G Y n i)) (ih x)

section Evaluation
open CategoryTheory
variable {C : Type t} [Category.{w} C] {obj : B → C}
/-- Evaluation composes the actual interpreted grade arrows, in traversal order. -/
def evaluate (act : ∀ {a b}, G a b → (obj a ⟶ obj b)) {a b} (p : Chain G a b) :
    obj a ⟶ obj b :=
  match p with
  | .nil _ => 𝟙 _
  | .cons g r => act g ≫ evaluate act r

theorem evaluate_append (act : ∀ {a b}, G a b → (obj a ⟶ obj b))
    {a b c} (p : Chain G a b) (q : Chain G b c) :
    evaluate (G := G) (obj := obj) act (append p q) = evaluate (G := G) (obj := obj) act p ≫ evaluate (G := G) (obj := obj) act q := by
  induction p with
  | nil => exact (Category.id_comp _).symm
  | cons g r ih =>
    change act g ≫ evaluate (G := G) (obj := obj) act (append r q) = (act g ≫ evaluate (G := G) (obj := obj) act r) ≫ evaluate (G := G) (obj := obj) act q
    rw [ih, Category.assoc]

theorem evaluate_flatten (act : ∀ {a b}, G a b → (obj a ⟶ obj b))
    {a b} (p : Chain (Chain G) a b) :
    evaluate (G := G) (obj := obj) act (flatten p) = evaluate (G := Chain G) (obj := obj) (fun p => evaluate (G := G) (obj := obj) act p) p := by
  induction p with
  | nil => rfl
  | cons q r ih => exact (evaluate_append (G := G) (obj := obj) act q (flatten r)).trans (congrArg (fun k => evaluate (G := G) (obj := obj) act q ≫ k) ih)
end Evaluation

theorem pack_length {X : B → Type (max u v w)} {a b} (p : Chain G a b) (x : X b) :
    (pack p x).1 = length p := by
  induction p with
  | nil => rfl
  | cons g r ih => exact congrArg Nat.succ (ih x)

/-- Free-monad multiplication on discrete payload families concatenates two dependent chains. -/
def joinValue {X : B → Type (max u v w)} {a} (z : Value.{u,v,w} G (Value.{u,v,w} G X) a) : Value.{u,v,w} G X a :=
  ⟨z.2.2.1,append z.2.1 z.2.2.2.1,z.2.2.2.2⟩

theorem joinValue_left {X : B → Type (max u v w)} {a} (z : Value.{u,v,w} G X a) :
    joinValue.{u,v,w} (emptyValue.{u,v,w} z) = z := rfl

theorem joinValue_right {X : B → Type (max u v w)} {a} (z : Value.{u,v,w} G X a) :
    joinValue.{u,v,w} (valueMap.{u,v,w} (fun _ x => emptyValue.{u,v,w} (G := G) x) z) = z := by
  rcases z with ⟨b,p,x⟩
  change (⟨b,append p (.nil b),x⟩ : Value.{u,v,w} G X a) = _
  rw [append_nil]

theorem joinValue_assoc {X : B → Type (max u v w)} {a} (z : Value.{u,v,w} G (Value.{u,v,w} G (Value.{u,v,w} G X)) a) :
    joinValue.{u,v,w} (joinValue.{u,v,w} z) = joinValue.{u,v,w} (valueMap.{u,v,w} (fun _ => joinValue.{u,v,w}) z) := by
  rcases z with ⟨b,p,c,q,d,r,x⟩
  change (⟨d,append (append p q) r,x⟩ : Value.{u,v,w} G X a) = _
  rw [append_assoc]
  rfl

/-- Concrete witness: at context n there are n+1 possible grades, and each extends to n+1. -/
def varyingSpan := fromExtension (fun n : Nat => Fin (n+1)) (fun n _ => n+1)

def varyingChain : Chain varyingSpan 0 2 :=
  .cons ⟨0,rfl⟩ (.cons (b := 2) ⟨1,rfl⟩ (.nil 2))

theorem varyingChain_length : length varyingChain = 2 := rfl

theorem varying_no_loop (n : Nat) : IsEmpty (varyingSpan n n) :=
  ⟨fun g => Nat.succ_ne_self n g.property⟩

theorem parallel_grades_distinct :
    singleton (G := varyingSpan) (a := 1) (b := 2) ⟨0,rfl⟩ ≠ singleton ⟨1,rfl⟩ := by
  intro h
  injection h with _ hg
  cases hg
  rename_i he _
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Subtype.val he)

theorem singleton_natural {H : Span.{u,w} B} (f : ∀ {a b}, G a b → H a b)
    {a b} (g : G a b) : map (G := G) (H := H) f (singleton g) = singleton (G := H) (f g) := rfl

theorem emptyValue_natural {X Y : B → Type (max u v w)} (f : ∀ b, X b → Y b)
    {a} (x : X a) : valueMap (G := G) f (emptyValue x) = emptyValue (f a x) := rfl

theorem joinValue_natural {X Y : B → Type (max u v w)} (f : ∀ b, X b → Y b)
    {a} (z : Value.{u,v,w} G (Value.{u,v,w} G X) a) :
    valueMap.{u,v,w} f (joinValue.{u,v,w} z) =
      joinValue.{u,v,w} (valueMap.{u,v,w} (fun _ => valueMap.{u,v,w} f) z) := rfl

section Evaluation
open CategoryTheory
variable {C : Type t} [Category.{w} C] {obj : B → C}
theorem evaluate_singleton (act : ∀ {a b}, G a b → (obj a ⟶ obj b))
    {a b} (g : G a b) : evaluate (G := G) (obj := obj) act (singleton g) = act g :=
  Category.comp_id _

/-- Any interpretation preserving nil and head action agrees on all complete dependent chains. -/
theorem evaluate_unique (act : ∀ {a b}, G a b → (obj a ⟶ obj b))
    (k : ∀ {a b}, Chain G a b → (obj a ⟶ obj b))
    (hn : ∀ a, k (.nil a) = 𝟙 (obj a))
    (hc : ∀ {a b c} (g : G a b) (p : Chain G b c), k (.cons g p) = act g ≫ k p)
    {a b} (p : Chain G a b) : k p = evaluate (G := G) (obj := obj) act p := by
  induction p with
  | nil a => exact hn a
  | cons g r ih => exact (hc g r).trans (congrArg (fun k => act g ≫ k) ih)
end Evaluation
end ContextualComposition.FiniteTelescope
