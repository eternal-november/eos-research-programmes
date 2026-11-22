module

public import Init

@[expose] public section

/-! Native families in a category with coherent addressed finite sums.
The additive input is the (forward-splitting) fragment of the pseudofunctor
of finite direct images. No direct sum is required to be a coproduct.
Only structural partition comparisons occur in its laws. -/
namespace ContextualComposition.NativeFinitePush
universe u v
structure Coeff (C : Type u) where
  Hom : C → C → Type v
  id : ∀ a, Hom a a
  seq : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  id_seq : ∀ {a b} (f : Hom a b), seq (id a) f = f
  seq_id : ∀ {a b} (f : Hom a b), seq f (id b) = f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    seq (seq f g) h = seq f (seq g h)

variable {C : Type u} (K : Coeff.{u,v} C)
abbrev Arr {n : Nat} (A B : Fin n → C) := ∀ i, K.Hom (A i) (B i)
def ids {n} (A : Fin n → C) : Arr K A A := fun i => K.id (A i)
def seq {n} {A B D : Fin n → C} (f : Arr K A B) (g : Arr K B D) : Arr K A D :=
  fun i => K.seq (f i) (g i)
theorem seq_assoc {n} {A B D E : Fin n → C} (f : Arr K A B) (g : Arr K B D) (h : Arr K D E) :
    seq K (seq K f g) h = seq K f (seq K g h) := funext fun _ => K.assoc _ _ _
theorem ids_seq {n} {A B : Fin n → C} (f : Arr K A B) : seq K (ids K A) f = f :=
  funext fun i => K.id_seq (f i)
theorem seq_ids {n} {A B : Fin n → C} (f : Arr K A B) : seq K f (ids K B) = f :=
  funext fun i => K.seq_id (f i)

/-- Sums indexed by each preimage, including empty preimages. Forward comparison
arrows suffice for the category theorem; invertibility is not used. -/
structure Push where
  obj : ∀ {n m}, (Fin n → Fin m) → (Fin n → C) → Fin m → C
  map : ∀ {n m} (f : Fin n → Fin m) {A B}, Arr K A B → Arr K (obj f A) (obj f B)
  map_id : ∀ {n m} (f : Fin n → Fin m) A, map f (ids K A) = ids K (obj f A)
  map_seq : ∀ {n m} (f : Fin n → Fin m) {A B D} (p : Arr K A B) (q : Arr K B D),
    map f (seq K p q) = seq K (map f p) (map f q)
  single : ∀ {n} (A : Fin n → C), Arr K (obj id A) A
  split : ∀ {n m l} (f : Fin n → Fin m) (g : Fin m → Fin l) A,
    Arr K (obj (g ∘ f) A) (obj g (obj f A))
  single_nat : ∀ {n} {A B : Fin n → C} (p : Arr K A B),
    seq K (map id p) (single B) = seq K (single A) p
  split_nat : ∀ {n m l} (f : Fin n → Fin m) (g : Fin m → Fin l) {A B} (p : Arr K A B),
    seq K (map (g ∘ f) p) (split f g B) = seq K (split f g A) (map g (map f p))
  left_unit : ∀ {n m} (f : Fin n → Fin m) A,
    seq K (split id f A) (map f (single A)) = ids K (obj f A)
  right_unit : ∀ {n m} (f : Fin n → Fin m) A,
    seq K (split f id A) (single (obj f A)) = ids K (obj f A)
  pent : ∀ {n m l r} (f : Fin n → Fin m) (g : Fin m → Fin l) (h : Fin l → Fin r) A,
    seq K (split (g ∘ f) h A) (map h (split f g A)) =
      seq K (split f (h ∘ g) A) (split g h (obj f A))

structure Family (C : Type u) where
  n : Nat
  val : Fin n → C
variable {K} (S : Push K)
structure Hom (A B : Family C) where
  addr : Fin A.n → Fin B.n
  cell : Arr K (S.obj addr A.val) B.val
namespace Hom
variable {S} {A B D E : Family C}
def ident (A : Family C) : Hom S A A := ⟨id, S.single A.val⟩
def comp (p : Hom S A B) (q : Hom S B D) : Hom S A D :=
  ⟨q.addr ∘ p.addr, seq K (S.split p.addr q.addr A.val) (seq K (S.map q.addr p.cell) q.cell)⟩
theorem ident_comp (p : Hom S A B) : comp (ident A) p = p := by
  cases p with
  | mk f a =>
    simp only [comp, ident, ← seq_assoc, S.left_unit]
    exact congrArg (Hom.mk f) (ids_seq K a)
theorem comp_ident (p : Hom S A B) : comp p (ident B) = p := by
  cases p with
  | mk f a =>
    simp only [comp, ident, S.single_nat, ← seq_assoc, S.right_unit]
    exact congrArg (Hom.mk f) (ids_seq K a)
theorem comp_assoc (p : Hom S A B) (q : Hom S B D) (r : Hom S D E) :
    comp (comp p q) r = comp p (comp q r) := by
  unfold comp
  congr 1
  rw [S.map_seq, S.map_seq]
  simp only [seq_assoc]
  rw [← seq_assoc K (S.split _ _ _) (S.map _ (S.split _ _ _)), S.pent]
  simp only [seq_assoc]
  rw [← seq_assoc K (S.split _ _ (S.obj _ _)) (S.map _ (S.map _ _)), ← S.split_nat]
  simp only [seq_assoc]
end Hom

/-- Collapse all addresses, then use a single global map to the unit. -/
def terminalShape (I : C) : Family C := ⟨1, fun _ => I⟩
structure Aug (I : C) where
  base : Family C
  ε : Hom S base (terminalShape I)
structure AugHom {I : C} (A B : Aug S I) where
  native : Hom S A.base B.base
  preserves : native.comp B.ε = A.ε
namespace AugHom
variable {S} {I : C} {A B D E : Aug S I}
def ident (A : Aug S I) : AugHom S A A :=
  ⟨Hom.ident A.base, Hom.ident_comp _⟩
def comp (a : AugHom S A B) (b : AugHom S B D) : AugHom S A D :=
  ⟨a.native.comp b.native, by rw [Hom.comp_assoc, b.preserves, a.preserves]⟩
theorem ext {a b : AugHom S A B} (h : a.native = b.native) : a = b := by
  cases a; cases b; cases h; rfl
theorem ident_comp (a : AugHom S A B) : comp (ident A) a = a := ext (Hom.ident_comp _)
theorem comp_ident (a : AugHom S A B) : comp a (ident B) = a := ext (Hom.comp_ident _)
theorem comp_assoc (a : AugHom S A B) (b : AugHom S B D) (c : AugHom S D E) :
    comp (comp a b) c = comp a (comp b c) := ext (Hom.comp_assoc _ _ _)
def unit (I : C) : Aug S I := ⟨terminalShape I, Hom.ident _⟩
def terminate (A : Aug S I) : AugHom S A (unit I) := ⟨A.ε, Hom.comp_ident _⟩
theorem terminal (a : AugHom S A (unit I)) : a = terminate A :=
  ext ((Hom.comp_ident a.native).symm.trans a.preserves)
end AugHom

/-- One concrete choice of addresses for the ordered whole preimage. Objects
can be pinned to literal sums without postulating comparison isomorphisms
between equal resource labels. -/
def fibreList {n m} (f : Fin n → Fin m) (j : Fin m) : List (Fin n) :=
  (List.finRange n).filter fun i => f i == j
theorem mem_fibreList {n m} {f : Fin n → Fin m} {i : Fin n} {j : Fin m} :
    i ∈ fibreList f j ↔ f i = j := by simp [fibreList]
def FoldPinned (total : List C → C) : Prop :=
  ∀ {n m} (f : Fin n → Fin m) (A : Fin n → C) j, S.obj f A j = total ((fibreList f j).map A)
theorem empty_fibre {total : List C → C} (h : FoldPinned S total)
    {n m} (f : Fin n → Fin m) (A : Fin n → C) (j : Fin m) (none : ∀ i, f i ≠ j) :
    S.obj f A j = total [] := by
  have e : fibreList f j = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => none i (mem_fibreList.mp hi)
  simp [h f A j, e]
end ContextualComposition.NativeFinitePush
