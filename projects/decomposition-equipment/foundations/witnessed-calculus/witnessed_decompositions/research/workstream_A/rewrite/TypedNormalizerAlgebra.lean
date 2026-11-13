import Mathlib.Data.ZMod.Basic

/-!
# Typed mixed rewrite algebra for the frozen A4 representative

This auxiliary file does not supply the graph-cut interpretation. It proves the
mixed normalization theorem for endpoint-indexed terms with arbitrary retained
leaf payloads. The endpoint category is the three-element chain. Decorations
range over an arbitrary commutative additive monoid, to be instantiated by ZMod 3.

`E` is generated independently by the seven declared equations and equivalence /
context closure. `quote` is a reducible, terminal-unit auxiliary expression;
`reify` uses the actual zero/one/many-frontier right-comb convention.
-/

namespace TypedNormalizer

abbrev Interface := Fin 3

universe u v

inductive Term (Block : Type u) (M : Type v) : Interface → Interface → Type (max u v)
  | leaf {a b : Interface} (arrow : a ≤ b) (block : Block) : Term Block M a b
  | unit (a : Interface) : Term Block M a a
  | cut {a b c : Interface} : Term Block M a b → Term Block M b c → Term Block M a c
  | deco {a b : Interface} (m : M) : Term Block M a b → Term Block M a b

inductive Spine (Block : Type u) : Interface → Interface → Type u
  | nil (a : Interface) : Spine Block a a
  | cons {a b c : Interface} (arrow : a ≤ b) (block : Block) :
      Spine Block b c → Spine Block a c
  deriving DecidableEq

namespace Spine
variable {Block : Type u}

def append {a b c : Interface} (s : Spine Block a b) (t : Spine Block b c) :
    Spine Block a c :=
  match s with
  | .nil _ => t
  | .cons h x rest => .cons h x (append rest t)

@[simp] theorem nil_append {a b : Interface} (s : Spine Block a b) :
    append (.nil a) s = s := rfl

@[simp] theorem cons_append {a b c d : Interface} (h : a ≤ b) (x : Block)
    (s : Spine Block b c) (t : Spine Block c d) :
    append (.cons h x s) t = .cons h x (append s t) := rfl

@[simp] theorem append_nil {a b : Interface} (s : Spine Block a b) :
    append s (.nil b) = s := by
  induction s with
  | nil => rfl
  | cons h x rest ih => simp [ih]

@[simp] theorem append_assoc {a b c d : Interface} (s : Spine Block a b)
    (t : Spine Block b c) (r : Spine Block c d) :
    append (append s t) r = append s (append t r) := by
  induction s with
  | nil => rfl
  | cons h x rest ih => simp [ih]

def length {a b : Interface} : Spine Block a b → Nat
  | .nil _ => 0
  | .cons _ _ s => 1 + length s

@[simp] theorem length_append {a b c : Interface} (s : Spine Block a b)
    (t : Spine Block b c) : length (append s t) = length s + length t := by
  induction s with
  | nil => simp [length]
  | cons h x rest ih => simp [length, ih, Nat.add_assoc]

/-- Ordered payloads, without forgetting that the authoritative spine is typed. -/
def blocks {a b : Interface} : Spine Block a b → List Block
  | .nil _ => []
  | .cons _ x s => x :: blocks s

@[simp] theorem blocks_append {a b c : Interface} (s : Spine Block a b)
    (t : Spine Block b c) : blocks (append s t) = blocks s ++ blocks t := by
  induction s with
  | nil => rfl
  | cons h x rest ih => simp [blocks, ih]

@[simp] theorem blocks_length {a b : Interface} (s : Spine Block a b) :
    s.blocks.length = s.length := by
  induction s with
  | nil => rfl
  | cons h x rest ih => simp [blocks, length, ih, Nat.add_comm]

/-- Change payload coordinates without changing any interface or arrow. -/
def map {Block' : Type v} (f : Block → Block') {a b : Interface} :
    Spine Block a b → Spine Block' a b
  | .nil a => .nil a
  | .cons h x s => .cons h (f x) (map f s)

@[simp] theorem blocks_map {Block' : Type v} (f : Block → Block') {a b : Interface}
    (s : Spine Block a b) : (map f s).blocks = s.blocks.map f := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [map, blocks, ih]

@[simp] theorem map_append {Block' : Type v} (f : Block → Block') {a b c : Interface}
    (s : Spine Block a b) (t : Spine Block b c) :
    map f (append s t) = append (map f s) (map f t) := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [map, ih]

theorem map_injective {Block' : Type v} (f : Block → Block') (hf : Function.Injective f)
    {a b : Interface} : Function.Injective (@map Block Block' f a b) := by
  intro s t h
  induction s with
  | nil a =>
      cases t with
      | nil => rfl
      | cons h' x' t' => cases h
  | @cons a b c hab x s ih =>
      cases t with
      | nil => cases h
      | @cons _ b' _ hab' x' t' =>
          simp only [map, Spine.cons.injEq] at h
          rcases h with ⟨rfl, hx, ht⟩
          have he : x = x' := hf hx
          subst x'
          exact congrArg (Spine.cons hab x) (ih (eq_of_heq ht))

/-- A coordinate change only needs to be injective on the actual payloads of the
two compared frontiers. This is useful for rank coordinates inside a fixed root. -/
theorem map_eq_of_injOn {Block' : Type v} (f : Block → Block') {a b : Interface}
    (s t : Spine Block a b)
    (hf : ∀ x ∈ s.blocks, ∀ y ∈ t.blocks, f x = f y → x = y)
    (h : s.map f = t.map f) : s = t := by
  induction s with
  | nil a =>
      cases t with
      | nil => rfl
      | cons h' x' t' => cases h
  | @cons a b c hab x s ih =>
      cases t with
      | nil => cases h
      | @cons _ b' _ hab' x' t' =>
          simp only [map, Spine.cons.injEq] at h
          rcases h with ⟨rfl, hx, ht⟩
          have he : x = x' := hf x (by simp [blocks]) x' (by simp [blocks]) hx
          subst x'
          apply congrArg (Spine.cons hab x)
          apply ih t'
          · intro y hy z hz hyz
            exact hf y (by simp [blocks, hy]) z (by simp [blocks, hz]) hyz
          · exact eq_of_heq ht

/-- A typed frontier entry for finite occurrence dispatch and external inspection. -/
structure Entry (Block : Type u) where
  source : Interface
  target : Interface
  arrow : source ≤ target
  block : Block
  deriving DecidableEq

/-- Ordered entries retain source, target, the chain arrow, and the payload. -/
def entries {a b : Interface} : Spine Block a b → List (Entry Block)
  | .nil _ => []
  | @cons _ a b c h x s => ⟨a, b, h, x⟩ :: entries s

@[simp] theorem entries_length {a b : Interface} (s : Spine Block a b) :
    s.entries.length = s.length := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [entries, length, ih, Nat.add_comm]

@[simp] theorem entries_append {a b c : Interface} (s : Spine Block a b)
    (t : Spine Block b c) : (s.append t).entries = s.entries ++ t.entries := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [entries, ih]

@[simp] theorem entries_blocks {a b : Interface} (s : Spine Block a b) :
    s.entries.map Entry.block = s.blocks := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [entries, blocks, ih]

end Spine

variable {Block : Type u} {M : Type v} [AddCommMonoid M]

/-- The full typed ordered frontier and its accumulated decoration. -/
abbrev NormalData (Block : Type u) (M : Type v) (a b : Interface) :=
  Spine Block a b × M

namespace Term

def frontier {a b : Interface} : Term Block M a b → Spine Block a b
  | .leaf h x => .cons h x (.nil _)
  | .unit a => .nil a
  | .cut s t => Spine.append (frontier s) (frontier t)
  | .deco _ s => frontier s

def weight {a b : Interface} : Term Block M a b → M
  | .leaf _ _ => 0
  | .unit _ => 0
  | .cut s t => weight s + weight t
  | .deco m s => m + weight s

def normalize {a b : Interface} (t : Term Block M a b) : NormalData Block M a b :=
  (frontier t, weight t)

end Term

/-- The independently generated mixed congruence. There is no semantic-equality
constructor, and its declaration does not refer to `normalize`. -/
inductive E : {a b : Interface} → Term Block M a b → Term Block M a b → Prop
  | refl {a b} (t : Term Block M a b) : E t t
  | symm {a b} {s t : Term Block M a b} : E s t → E t s
  | trans {a b} {s t r : Term Block M a b} : E s t → E t r → E s r
  | cut {a b c} {s s' : Term Block M a b} {t t' : Term Block M b c} :
      E s s' → E t t' → E (.cut s t) (.cut s' t')
  | deco {a b} (m : M) {s t : Term Block M a b} : E s t → E (.deco m s) (.deco m t)
  | R {a b c d} (s : Term Block M a b) (t : Term Block M b c)
      (r : Term Block M c d) : E (.cut (.cut s t) r) (.cut s (.cut t r))
  | UL {a b} (s : Term Block M a b) : E (.cut (.unit a) s) s
  | UR {a b} (s : Term Block M a b) : E (.cut s (.unit b)) s
  | D0 {a b} (s : Term Block M a b) : E (.deco 0 s) s
  | DA {a b} (m n : M) (s : Term Block M a b) :
      E (.deco m (.deco n s)) (.deco (m + n) s)
  | DL {a b c} (m : M) (s : Term Block M a b) (t : Term Block M b c) :
      E (.cut (.deco m s) t) (.deco m (.cut s t))
  | DR {a b c} (m : M) (s : Term Block M a b) (t : Term Block M b c) :
      E (.cut s (.deco m t)) (.deco m (.cut s t))

namespace E

theorem sound {a b : Interface} {s t : Term Block M a b} (h : E s t) :
    s.normalize = t.normalize := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cut _ _ ih₁ ih₂ =>
      have hf₁ := congrArg Prod.fst ih₁
      have hw₁ := congrArg Prod.snd ih₁
      have hf₂ := congrArg Prod.fst ih₂
      have hw₂ := congrArg Prod.snd ih₂
      exact Prod.ext (congrArg₂ Spine.append hf₁ hf₂) (congrArg₂ (· + ·) hw₁ hw₂)
  | deco m _ ih =>
      have hf := congrArg Prod.fst ih
      have hw := congrArg (m + ·) (congrArg Prod.snd ih)
      apply Prod.ext
      · exact hf
      · exact hw
  | R => simp [Term.normalize, Term.frontier, Term.weight, add_assoc]
  | UL => simp [Term.normalize, Term.frontier, Term.weight]
  | UR => simp [Term.normalize, Term.frontier, Term.weight]
  | D0 => simp [Term.normalize, Term.frontier, Term.weight]
  | DA => simp [Term.normalize, Term.frontier, Term.weight, add_assoc]
  | DL => simp [Term.normalize, Term.frontier, Term.weight, add_assoc]
  | DR => simp [Term.normalize, Term.frontier, Term.weight, add_left_comm]

end E

namespace Spine

/-- Auxiliary terminal-unit quoting, not an irreducible normal form. -/
def quote {a b : Interface} : Spine Block a b → Term Block M a b
  | .nil a => .unit a
  | .cons h x s => .cut (.leaf h x) (quote s)

/-- Prepending a leaf suppresses the auxiliary terminal unit precisely when
its typed tail has no external occurrences. -/
def prepend {a b c : Interface} (h : a ≤ b) (x : Block) (s : Spine Block b c) :
    Term Block M b c → Term Block M a c :=
  match s with
  | .nil _ => fun _ => .leaf h x
  | .cons _ _ _ => fun t => .cut (.leaf h x) t

/-- Actual bare right comb: the singleton case is an external identity leaf. -/
def comb {a b : Interface} (s : Spine Block a b) : Term Block M a b :=
  match s with
  | .nil a => .unit a
  | .cons h x rest => prepend h x rest (comb rest)
termination_by structural s

omit [AddCommMonoid M] in
@[simp] theorem frontier_quote {a b : Interface} (s : Spine Block a b) :
    (quote (M := M) s).frontier = s := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [quote, Term.frontier, ih]

@[simp] theorem weight_quote {a b : Interface} (s : Spine Block a b) :
    (quote (M := M) s).weight = 0 := by
  induction s with
  | nil => rfl
  | cons h x s ih => simp [quote, Term.weight, ih]

theorem quote_append {a b c : Interface} (s : Spine Block a b) (t : Spine Block b c) :
    E (.cut (quote (M := M) s) (quote t)) (quote (append s t)) := by
  induction s with
  | nil => exact E.UL _
  | cons h x s ih =>
      exact E.trans (E.R _ _ _) (E.cut (E.refl _) (ih t))

theorem quote_equiv_comb {a b : Interface} (s : Spine Block a b) :
    E (quote (M := M) s) (comb (M := M) s) := by
  induction s with
  | nil a => simpa only [quote, comb, prepend] using E.refl (Term.unit (Block := Block) (M := M) a)
  | cons h x s ih =>
      cases s with
      | nil => simpa only [quote, comb, prepend] using E.UR (Term.leaf (M := M) h x)
      | cons h' x' s' =>
          simpa only [quote, comb, prepend] using E.cut (E.refl (Term.leaf h x)) ih

@[simp] theorem frontier_comb {a b : Interface} (s : Spine Block a b) :
    (comb (M := M) s).frontier = s := by
  have h := congrArg Prod.fst (E.sound (quote_equiv_comb (M := M) s))
  simpa [Term.normalize] using h.symm

@[simp] theorem weight_comb {a b : Interface} (s : Spine Block a b) :
    (comb (M := M) s).weight = 0 := by
  have h := congrArg Prod.snd (E.sound (quote_equiv_comb (M := M) s))
  simpa [Term.normalize] using h.symm

end Spine

/-- Executable canonical form, omitting the zero root decoration. -/
def reify [DecidableEq M] {a b : Interface} (n : NormalData Block M a b) : Term Block M a b :=
  if n.2 = 0 then n.1.comb else .deco n.2 n.1.comb

@[simp] theorem normalize_reify [DecidableEq M] {a b : Interface}
    (n : NormalData Block M a b) : (reify n).normalize = n := by
  rcases n with ⟨s, m⟩
  by_cases hm : m = 0 <;> simp [reify, hm, Term.normalize, Term.frontier, Term.weight]

theorem term_equiv_quote_normalize {a b : Interface} (t : Term Block M a b) :
    E t (.deco t.weight t.frontier.quote) := by
  induction t with
  | leaf h x =>
      exact E.trans (E.symm (E.UR _)) (E.symm (E.D0 _))
  | unit a => exact E.symm (E.D0 _)
  | cut s t ihs iht =>
      exact E.trans (E.cut ihs iht)
        (E.trans (E.DL _ _ _)
          (E.trans (E.deco _ (E.DR _ _ _))
            (E.trans (E.DA _ _ _) (E.deco _ (Spine.quote_append _ _)))))
  | deco m t ih =>
      exact E.trans (E.deco m ih) (E.DA _ _ _)

theorem term_equiv_reify_normalize [DecidableEq M] {a b : Interface}
    (t : Term Block M a b) : E t (reify t.normalize) := by
  refine E.trans (term_equiv_quote_normalize t) ?_
  refine E.trans (E.deco _ (Spine.quote_equiv_comb _)) ?_
  by_cases hm : t.weight = 0
  · simpa [reify, Term.normalize, hm] using E.D0 (t.frontier.comb (M := M))
  · simp only [reify, Term.normalize, hm, ↓reduceIte]
    exact E.refl _

/-- Reification does not identify different full typed normal data. -/
theorem reify_injective [DecidableEq M] {a b : Interface} :
    Function.Injective (@reify Block M _ _ a b) := by
  intro n n' h
  have hn := congrArg Term.normalize h
  simpa only [normalize_reify] using hn

/-- Soundness and completeness for the independently generated equations. -/
theorem equiv_iff_normalize_eq [DecidableEq M] {a b : Interface}
    (s t : Term Block M a b) : E s t ↔ s.normalize = t.normalize := by
  constructor
  · exact E.sound
  · intro h
    exact E.trans (term_equiv_reify_normalize s)
      (h ▸ E.symm (term_equiv_reify_normalize t))

namespace Term

/-- Number of external occurrences; nullary units contribute no occurrence. -/
def leafCount {a b : Interface} : Term Block M a b → Nat
  | .leaf _ _ => 1
  | .unit _ => 0
  | .cut s t => leafCount s + leafCount t
  | .deco _ s => leafCount s

omit [AddCommMonoid M] in
@[simp] theorem frontier_length {a b : Interface} (t : Term Block M a b) :
    t.frontier.length = t.leafCount := by
  induction t with
  | leaf => rfl
  | unit => rfl
  | cut s t ihs iht => simp [frontier, leafCount, ihs, iht]
  | deco m t ih => exact ih

/-- A property at every actual external occurrence, traversed using exactly the
offsets used by `subst`. Empty units contribute no condition. -/
def AllLeaves {a b : Interface} (t : Term Block M a b)
    (P : Nat → Spine.Entry Block → Prop) (offset : Nat := 0) : Prop :=
  match t with
  | @leaf _ _ a b h x => P offset ⟨a, b, h, x⟩
  | .unit _ => True
  | .cut s t => AllLeaves s P offset ∧ AllLeaves t P (offset + s.leafCount)
  | .deco _ s => AllLeaves s P offset

/-- Auxiliary recursive traversal of an entry list. -/
def EntryAll (P : Nat → Spine.Entry Block → Prop) (offset : Nat) :
    List (Spine.Entry Block) → Prop
  | [] => True
  | e :: es => P offset e ∧ EntryAll P (offset + 1) es

theorem entryAll_append (P : Nat → Spine.Entry Block → Prop)
    (s t : List (Spine.Entry Block)) (offset : Nat) :
    EntryAll P offset (s ++ t) ↔
      EntryAll P offset s ∧ EntryAll P (offset + s.length) t := by
  induction s generalizing offset with
  | nil => simp [EntryAll]
  | cons e es ih =>
      simp only [List.cons_append, EntryAll, ih, List.length_cons]
      simp only [and_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem entryAll_iff_get (P : Nat → Spine.Entry Block → Prop)
    (s : List (Spine.Entry Block)) (offset : Nat) :
    EntryAll P offset s ↔ ∀ i : Fin s.length, P (offset + i.val) (s.get i) := by
  induction s generalizing offset with
  | nil => simp [EntryAll]
  | cons e es ih =>
      constructor
      · intro h i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using h.1
        · have hj := (ih (offset + 1)).mp h.2 j
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hj
      · intro h
        constructor
        · simpa using h 0
        · apply (ih (offset + 1)).mpr
          intro j
          have hj := h j.succ
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hj

omit [AddCommMonoid M] in
theorem allLeaves_iff_entryAll {a b : Interface} (t : Term Block M a b)
    (P : Nat → Spine.Entry Block → Prop) (offset : Nat := 0) :
    AllLeaves t P offset ↔ EntryAll P offset t.frontier.entries := by
  induction t generalizing offset with
  | leaf h x => simp [AllLeaves, frontier, Spine.entries, EntryAll]
  | unit a => simp [AllLeaves, frontier, Spine.entries, EntryAll]
  | cut s t ihs iht =>
      simp only [AllLeaves, frontier, Spine.entries_append, entryAll_append,
        Spine.entries_length, frontier_length, ihs, iht]
  | deco m t ih => exact ih offset

omit [AddCommMonoid M] in
/-- Exact traversal theorem connecting recursive substitution offsets to the
ordered finite frontier, including units, empty frontiers and repeated payloads. -/
theorem allLeaves_iff_entries {a b : Interface} (t : Term Block M a b)
    (P : Nat → Spine.Entry Block → Prop) (offset : Nat := 0) :
    AllLeaves t P offset ↔
      ∀ i : Fin t.frontier.entries.length,
        P (offset + i.val) (t.frontier.entries.get i) :=
  (allLeaves_iff_entryAll t P offset).trans (entryAll_iff_get P t.frontier.entries offset)

/-- A replacement depends on the ordered occurrence index as well as its full
leaf type. Equal payloads at distinct positions can receive different terms. -/
abbrev Substitution (Block : Type u) (M : Type v) :=
  ∀ (_position : Nat) {a b : Interface}, a ≤ b → Block → Term Block M a b

/-- Simultaneous occurrence-wise substitution. `offset` locates this subtree in
an external ordered frontier; it is not a leaf-name lookup. -/
def subst {a b : Interface} (t : Term Block M a b) (σ : Substitution Block M)
    (offset : Nat := 0) : Term Block M a b :=
  match t with
  | .leaf h x => σ offset h x
  | .unit a => .unit a
  | .cut s t => .cut (subst s σ offset) (subst t σ (offset + s.leafCount))
  | .deco m s => .deco m (subst s σ offset)

theorem subst_congr {a b : Interface} (t : Term Block M a b)
    (σ τ : Substitution Block M)
    (h : ∀ n {a b} (hab : a ≤ b) x, E (σ n hab x) (τ n hab x))
    (offset : Nat := 0) : E (t.subst σ offset) (t.subst τ offset) := by
  induction t generalizing offset with
  | leaf hab x => exact h offset hab x
  | unit a => exact E.refl _
  | cut s t ihs iht => exact E.cut (ihs offset) (iht _)
  | deco m t ih => exact E.deco m (ih offset)

end Term

namespace E

theorem frontier_eq {a b : Interface} {s t : Term Block M a b} (h : E s t) :
    s.frontier = t.frontier := congrArg Prod.fst h.sound

theorem leafCount_eq {a b : Interface} {s t : Term Block M a b} (h : E s t) :
    s.leafCount = t.leafCount := by
  simpa only [Term.frontier_length] using congrArg Spine.length h.frontier_eq

/-- The independently generated congruence is closed under arbitrary well-typed
occurrence-wise substitution, including different replacements of equal leaves. -/
theorem subst {a b : Interface} {s t : Term Block M a b} (h : E s t)
    (σ : Term.Substitution Block M) (offset : Nat := 0) :
    E (s.subst σ offset) (t.subst σ offset) := by
  induction h generalizing offset with
  | refl => exact E.refl _
  | symm _ ih => exact E.symm (ih offset)
  | trans _ _ ih₁ ih₂ => exact E.trans (ih₁ offset) (ih₂ offset)
  | cut hs ht ihs iht =>
      simp only [Term.subst]
      rw [hs.leafCount_eq]
      exact E.cut (ihs offset) (iht _)
  | deco m h ih => exact E.deco m (ih offset)
  | R s t r =>
      simpa only [Term.subst, Term.leafCount, Nat.add_assoc] using
        E.R (s.subst σ offset) (t.subst σ (offset + s.leafCount))
          (r.subst σ (offset + s.leafCount + t.leafCount))
  | UL s => simpa only [Term.subst, Term.leafCount, Nat.add_zero] using E.UL (s.subst σ offset)
  | UR s => exact E.UR (s.subst σ offset)
  | D0 s => exact E.D0 (s.subst σ offset)
  | DA m n s => exact E.DA m n (s.subst σ offset)
  | DL m s t => exact E.DL m (s.subst σ offset) (t.subst σ (offset + s.leafCount))
  | DR m s t => exact E.DR m (s.subst σ offset) (t.subst σ (offset + s.leafCount))

end E

/-- Equality in the declared presentation is decidable by executable full-data
normalization, not by an enumeration bound on term size. -/
instance decidableE [DecidableEq Block] [DecidableEq M] {a b : Interface}
    (s t : Term Block M a b) : Decidable (E s t) :=
  decidable_of_iff (s.normalize = t.normalize) (equiv_iff_normalize_eq s t).symm

/-- The seven oriented local rules, with closure under every one-hole context. -/
inductive Step : {a b : Interface} → Term Block M a b → Term Block M a b → Prop
  | R {a b c d} (s : Term Block M a b) (t : Term Block M b c)
      (r : Term Block M c d) : Step (.cut (.cut s t) r) (.cut s (.cut t r))
  | UL {a b} (s : Term Block M a b) : Step (.cut (.unit a) s) s
  | UR {a b} (s : Term Block M a b) : Step (.cut s (.unit b)) s
  | D0 {a b} (s : Term Block M a b) : Step (.deco 0 s) s
  | DA {a b} (m n : M) (s : Term Block M a b) :
      Step (.deco m (.deco n s)) (.deco (m + n) s)
  | DL {a b c} (m : M) (s : Term Block M a b) (t : Term Block M b c) :
      Step (.cut (.deco m s) t) (.deco m (.cut s t))
  | DR {a b c} (m : M) (s : Term Block M a b) (t : Term Block M b c) :
      Step (.cut s (.deco m t)) (.deco m (.cut s t))
  | cut_left {a b c} {s s' : Term Block M a b} (t : Term Block M b c) :
      Step s s' → Step (.cut s t) (.cut s' t)
  | cut_right {a b c} (s : Term Block M a b) {t t' : Term Block M b c} :
      Step t t' → Step (.cut s t) (.cut s t')
  | deco {a b} (m : M) {s t : Term Block M a b} :
      Step s t → Step (.deco m s) (.deco m t)

theorem Step.toE {a b : Interface} {s t : Term Block M a b} (h : Step s t) : E s t := by
  induction h with
  | R => exact E.R _ _ _
  | UL => exact E.UL _
  | UR => exact E.UR _
  | D0 => exact E.D0 _
  | DA => exact E.DA _ _ _
  | DL => exact E.DL _ _ _
  | DR => exact E.DR _ _ _
  | cut_left t _ ih => exact E.cut ih (E.refl t)
  | cut_right s _ ih => exact E.cut (E.refl s) ih
  | deco m _ ih => exact E.deco m ih

namespace Term

/-- This predicate recognizes external leaves, never nullary units. -/
def IsLeaf {a b : Interface} : Term Block M a b → Prop
  | .leaf _ _ => True
  | _ => False

/-- Nonempty undecorated right comb with no terminal nullary. -/
def IsChain {a b : Interface} : Term Block M a b → Prop
  | .leaf _ _ => True
  | .cut s t => s.IsLeaf ∧ t.IsChain
  | _ => False

def IsBare {a b : Interface} : Term Block M a b → Prop
  | .unit _ => True
  | t => t.IsChain

/-- The selected canonical syntax, including a nonzero optional root decorator. -/
def IsNormal {a b : Interface} : Term Block M a b → Prop
  | .deco m t => m ≠ 0 ∧ t.IsBare
  | t => t.IsBare

theorem isChain_isNormal {a b : Interface} {t : Term Block M a b} (h : t.IsChain) :
    t.IsNormal := by
  cases t <;> simp_all [IsChain, IsNormal, IsBare]

theorem isBare_isNormal {a b : Interface} {t : Term Block M a b} (h : t.IsBare) :
    t.IsNormal := by
  cases t <;> simp_all [IsChain, IsNormal, IsBare]

end Term

theorem Step.not_isLeaf {a b : Interface} {s t : Term Block M a b} (h : Step s t) :
    ¬s.IsLeaf := by
  cases h <;> simp [Term.IsLeaf]

/-- Every recognized normal expression is irreducible under the exact rules,
including redexes in arbitrary contexts. -/
theorem Step.not_isNormal {a b : Interface} {s t : Term Block M a b} (h : Step s t) :
    ¬s.IsNormal := by
  induction h with
  | R => simp [Term.IsNormal, Term.IsBare, Term.IsChain, Term.IsLeaf]
  | UL => simp [Term.IsNormal, Term.IsBare, Term.IsChain, Term.IsLeaf]
  | UR => simp [Term.IsNormal, Term.IsBare, Term.IsChain, Term.IsLeaf]
  | D0 => simp [Term.IsNormal]
  | DA => simp [Term.IsNormal, Term.IsBare, Term.IsChain]
  | DL => simp [Term.IsNormal, Term.IsBare, Term.IsChain, Term.IsLeaf]
  | DR => simp [Term.IsNormal, Term.IsBare, Term.IsChain, Term.IsLeaf]
  | cut_left t h ih =>
      intro hn
      exact h.not_isLeaf hn.1
  | cut_right s h ih =>
      intro hn
      exact ih (Term.isChain_isNormal hn.2)
  | deco m h ih =>
      intro hn
      exact ih (Term.isBare_isNormal hn.2)

namespace Spine

theorem comb_isChain {a b : Interface} (s : Spine Block a b) (h : 0 < s.length) :
    (s.comb (M := M)).IsChain := by
  induction s with
  | nil => simp [length] at h
  | cons hab x s ih =>
      cases s with
      | nil => simp only [comb, prepend, Term.IsChain]
      | cons hbc y t =>
          simp only [comb, prepend, Term.IsChain, Term.IsLeaf]
          exact ⟨True.intro, ih (by simp [length])⟩

theorem comb_isBare {a b : Interface} (s : Spine Block a b) :
    (s.comb (M := M)).IsBare := by
  cases s with
  | nil => simp only [comb, prepend, Term.IsBare]
  | cons h x s =>
      have hchain := comb_isChain (M := M) (Spine.cons h x s) (by simp [length])
      cases s <;> simpa only [comb, prepend, Term.IsBare, Term.IsChain] using hchain

end Spine

theorem reify_isNormal [DecidableEq M] {a b : Interface} (n : NormalData Block M a b) :
    (reify n).IsNormal := by
  unfold reify
  split_ifs with h
  · exact Term.isBare_isNormal (Spine.comb_isBare n.1)
  · exact ⟨h, Spine.comb_isBare n.1⟩

theorem reify_irreducible [DecidableEq M] {a b : Interface} (n : NormalData Block M a b)
    (t : Term Block M a b) : ¬Step (reify n) t :=
  fun h => h.not_isNormal (reify_isNormal n)

/-- Even an empty-colour identity leaf remains one external occurrence and
cannot be erased by the nullary unit rules. -/
theorem identity_leaf_not_equiv_unit (a : Interface) (x : Block) :
    ¬E (Term.leaf (M := M) (le_refl a) x) (Term.unit a) := by
  intro h
  have hc := h.leafCount_eq
  simp [Term.leafCount] at hc

/-- An explicit, reusable interaction of both movement rules and aggregation. -/
theorem both_decorations_aggregate {a b c : Interface} (m n : M)
    (s : Term Block M a b) (t : Term Block M b c) :
    E (.cut (.deco m s) (.deco n t)) (.deco (m + n) (.cut s t)) :=
  E.trans (E.DL _ _ _) (E.trans (E.deco _ (E.DR _ _ _)) (E.DA _ _ _))

#print axioms Term.allLeaves_iff_entries
#print axioms Term.normalize
#print axioms reify
#print axioms Spine.comb
#print axioms Spine.quote_equiv_comb
#print axioms E.sound
#print axioms term_equiv_reify_normalize
#print axioms equiv_iff_normalize_eq
#print axioms E.subst
#print axioms reify_irreducible
#print axioms Spine.map_injective
#print axioms Spine.map_eq_of_injOn
#print axioms decidableE

end TypedNormalizer
