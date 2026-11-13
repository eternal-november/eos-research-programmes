import Mathlib.Data.Set.Image
set_option autoImplicit false

/-! Exact decoding of complete joint records, and independent deterministic
congruence. `Y` is the type of an entire retained record, not a marginal. -/
namespace JointQuotientDecoder
universe u v w z

variable {X : Type u} {Y : Type v} {Q : Type w} {R : Type z}

def RecordImage (P : X → Y → Prop) (r : Y → R) (x : X) (b : R) : Prop :=
  ∃ y, P x y ∧ r y = b

def Sound (P : X → Y → Prop) (A : Q → R → Prop) (q : X → Q) (r : Y → R) : Prop :=
  ∀ x y, P x y → A (q x) (r y)

def SourceFixedLift (P : X → Y → Prop) (A : Q → R → Prop)
    (q : X → Q) (r : Y → R) : Prop :=
  ∀ x b, A (q x) b → RecordImage P r x b

def ExactDecoder (P : X → Y → Prop) (A : Q → R → Prop)
    (q : X → Q) (r : Y → R) : Prop :=
  ∀ x b, A (q x) b ↔ RecordImage P r x b

/-- The exact image equation is both soundness and lifting at every chosen
source, rather than lifting at some representative of its code. -/
theorem exact_iff_sound_and_sourceFixedLift (P : X → Y → Prop)
    (A : Q → R → Prop) (q : X → Q) (r : Y → R) :
    ExactDecoder P A q r ↔ Sound P A q r ∧ SourceFixedLift P A q r := by
  constructor
  · intro h
    constructor
    · intro x y hy
      exact (h x (r y)).mpr ⟨y, hy, rfl⟩
    · intro x b hb
      exact (h x b).mp hb
  · rintro ⟨hs, hl⟩ x b
    constructor
    · exact hl x b
    · rintro ⟨y, hy, rfl⟩
      exact hs x y hy

def Stable (P : X → Y → Prop) (q : X → Q) (r : Y → R) : Prop :=
  ∀ x x', q x = q x' → ∀ b, RecordImage P r x b ↔ RecordImage P r x' b

/-- Candidate decoder formed by taking the union over all representatives. -/
def QuotientRelation (P : X → Y → Prop) (q : X → Q) (r : Y → R)
    (a : Q) (b : R) : Prop :=
  ∃ x, q x = a ∧ RecordImage P r x b

theorem quotient_exact_iff_stable (P : X → Y → Prop) (q : X → Q) (r : Y → R) :
    ExactDecoder P (QuotientRelation P q r) q r ↔ Stable P q r := by
  constructor
  · intro h x x' he b
    constructor
    · intro hx
      exact (h x' b).mp ⟨x, he, hx⟩
    · intro hx'
      exact (h x b).mp ⟨x', he.symm, hx'⟩
  · intro h x b
    constructor
    · rintro ⟨x', he, hx'⟩
      exact (h x' x he b).mp hx'
    · intro hx
      exact ⟨x, rfl, hx⟩

theorem exists_exact_iff_stable (P : X → Y → Prop) (q : X → Q) (r : Y → R) :
    (∃ A, ExactDecoder P A q r) ↔ Stable P q r := by
  constructor
  · rintro ⟨A, h⟩ x x' he b
    rw [← h x b, ← h x' b, he]
  · intro h
    exact ⟨QuotientRelation P q r, (quotient_exact_iff_stable P q r).mpr h⟩

/-- Unreachable abstract sources need not have unique arbitrary decoder rows.
Surjectivity is used exactly for uniqueness on the whole abstract carrier. -/
theorem exact_decoder_unique (P : X → Y → Prop) (q : X → Q) (r : Y → R)
    (hq : Function.Surjective q) {A B : Q → R → Prop}
    (ha : ExactDecoder P A q r) (hb : ExactDecoder P B q r) : A = B := by
  funext a b
  obtain ⟨x, rfl⟩ := hq a
  exact propext ((ha x b).trans (hb x b).symm)

/-- A predicate on a complete encoded record is interpreted using one witness.
This includes correlated predicates and the empty-record case. -/
theorem joint_test_preserved (P : X → Y → Prop) (A : Q → R → Prop)
    (q : X → Q) (r : Y → R) (h : ExactDecoder P A q r)
    (test : R → Prop) (x : X) :
    (∃ b, A (q x) b ∧ test b) ↔ ∃ y, P x y ∧ test (r y) := by
  constructor
  · rintro ⟨b, hb, ht⟩
    obtain ⟨y, hy, he⟩ := (h x b).mp hb
    exact ⟨y, hy, he ▸ ht⟩
  · rintro ⟨y, hy, ht⟩
    exact ⟨r y, (h x (r y)).mpr ⟨y, hy, rfl⟩, ht⟩

/-- Deterministic substitution or transport is a separate obligation. -/
def KernelCompatible {Z : Type*} {S : Type*}
    (q : X → Q) (r : Z → S) (f : X → Z) : Prop :=
  ∀ x x', q x = q x' → r (f x) = r (f x')

def Descends {Z : Type*} {S : Type*}
    (q : X → Q) (r : Z → S) (f : X → Z) : Prop :=
  ∃ g : Q → S, ∀ x, g (q x) = r (f x)

theorem descends_iff_kernelCompatible {Z : Type*} {S : Type*}
    (q : X → Q) (r : Z → S) (f : X → Z) (hq : Function.Surjective q) :
    Descends q r f ↔ KernelCompatible q r f := by
  constructor
  · rintro ⟨g, hg⟩ x x' he
    rw [← hg x, ← hg x', he]
  · intro hc
    classical
    let s : Q → X := fun a => Classical.choose (hq a)
    have hs : ∀ a, q (s a) = a := fun a => Classical.choose_spec (hq a)
    refine ⟨fun a => r (f (s a)), ?_⟩
    intro x
    exact hc (s (q x)) x (hs (q x))

theorem descent_unique {Z : Type*} {S : Type*}
    (q : X → Q) (r : Z → S) (f : X → Z) (hq : Function.Surjective q)
    {g g' : Q → S} (hg : ∀ x, g (q x) = r (f x))
    (hg' : ∀ x, g' (q x) = r (f x)) : g = g' := by
  funext a
  obtain ⟨x, rfl⟩ := hq a
  exact (hg x).trans (hg' x).symm

/-- Commuting squares for two deterministic operations compose. -/
theorem descent_composes {Z W S T : Type*} (q : X → Q) (r : Z → S)
    (s : W → T) (f : X → Z) (g : Z → W) (f' : Q → S) (g' : S → T)
    (hf : ∀ x, f' (q x) = r (f x))
    (hg : ∀ z, g' (r z) = s (g z)) :
    ∀ x, (g' ∘ f') (q x) = s ((g ∘ f) x) := by
  intro x
  change g' (f' (q x)) = s (g (f x))
  rw [hf, hg]

/-- A dependent tuple retains every typed occurrence as a separate coordinate. -/
def tupleEncode {I : Type*} {C D : I → Type*}
    (e : ∀ i, C i → D i) (x : ∀ i, C i) : ∀ i, D i := fun i => e i (x i)

theorem tupleEncode_surjective {I : Type*} {C D : I → Type*}
    (e : ∀ i, C i → D i) (he : ∀ i, Function.Surjective (e i)) :
    Function.Surjective (tupleEncode e) := by
  classical
  intro y
  refine ⟨fun i => Classical.choose (he i (y i)), ?_⟩
  funext i
  exact Classical.choose_spec (he i (y i))

/-- Exact criterion for an occurrence-indexed graft to descend. It is independent
of exactness of any cut decoder. In particular, cut stability alone is not enough. -/
theorem graft_descends_iff {I : Type*} {C D : I → Type*} {Z S : Type*}
    (e : ∀ i, C i → D i) (r : Z → S) (graft : (∀ i, C i) → Z)
    (he : ∀ i, Function.Surjective (e i)) :
    Descends (tupleEncode e) r graft ↔
      ∀ a b, (∀ i, e i (a i) = e i (b i)) → r (graft a) = r (graft b) := by
  rw [descends_iff_kernelCompatible _ _ _ (tupleEncode_surjective e he)]
  constructor
  · intro h a b hab
    exact h a b (funext hab)
  · intro h a b hab
    exact h a b (fun i => congrFun hab i)

/-- Exact records compose by retaining the intermediate witness. -/
theorem exact_compose_records {Z S : Type*}
    (P : X → Y → Prop) (T : Y → Z → Prop)
    (A : Q → R → Prop) (B : R → S → Prop)
    (q : X → Q) (r : Y → R) (s : Z → S)
    (hP : ExactDecoder P A q r) (hT : ExactDecoder T B r s) :
    ExactDecoder (fun x (yz : Y × Z) => P x yz.1 ∧ T yz.1 yz.2)
      (fun a (bc : R × S) => A a bc.1 ∧ B bc.1 bc.2)
      q (fun yz => (r yz.1, s yz.2)) := by
  intro x bc
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨y, hxy, hy⟩ := (hP x bc.1).mp hA
    obtain ⟨z, hyz, hz⟩ := (hT y bc.2).mp (hy ▸ hB)
    exact ⟨(y,z), ⟨hxy,hyz⟩, Prod.ext hy hz⟩
  · rintro ⟨⟨y,z⟩, ⟨hxy,hyz⟩, he⟩
    have hy : r y = bc.1 := congrArg Prod.fst he
    have hz : s z = bc.2 := congrArg Prod.snd he
    constructor
    · exact hy ▸ (hP x (r y)).mpr ⟨y,hxy,rfl⟩
    · rw [← hy, ← hz]
      exact (hT y (s z)).mpr ⟨z,hyz,rfl⟩


/-- The query language fixes its observable atoms, typed deterministic steps,
and joint cut shapes before choosing a quotient. -/
structure Signature where
  sorts : Type
  Atom : sorts → Type
  Step : sorts → sorts → Type
  Cut : sorts → Type
  arity : {s : sorts} → Cut s → Nat
  input : {s : sorts} → (c : Cut s) → Fin (arity c) → sorts

inductive Test (L : Signature) : L.sorts → Type where
  | atom {s} (a : L.Atom s) : Test L s
  | neg {s} (p : Test L s) : Test L s
  | conj {s} (p q : Test L s) : Test L s
  | step {s t} (f : L.Step s t) (p : Test L t) : Test L s
  | cut {s} (c : L.Cut s) (p : (i : Fin (L.arity c)) → Test L (L.input c i)) : Test L s

structure Model (L : Signature) where
  State : L.sorts → Type
  atom : {s : L.sorts} → L.Atom s → State s → Prop
  step : {s t : L.sorts} → L.Step s t → State s → State t
  cut : {s : L.sorts} → (c : L.Cut s) → State s →
    ((i : Fin (L.arity c)) → State (L.input c i)) → Prop

def holds {L : Signature} (M : Model L) : {s : L.sorts} → Test L s → M.State s → Prop
  | _, .atom a, x => M.atom a x
  | _, .neg p, x => ¬ holds M p x
  | _, .conj p q, x => holds M p x ∧ holds M q x
  | _, .step f p, x => holds M p (M.step f x)
  | _, .cut c p, x => ∃ ys, M.cut c x ys ∧ ∀ i, holds M (p i) (ys i)

/-- Soundness for every generated finite typed Boolean/step/joint-cut test.
The cut case chooses ONE whole tuple before interpreting all child tests.
A nullary tuple has a vacuous child conjunction, but cut feasibility remains. -/
theorem generated_tests_preserved {L : Signature} (M N : Model L)
    (q : (s : L.sorts) → M.State s → N.State s)
    (ha : ∀ s (a : L.Atom s) x, N.atom a (q s x) ↔ M.atom a x)
    (hs : ∀ s t (f : L.Step s t) x, N.step f (q s x) = q t (M.step f x))
    (hc : ∀ s (c : L.Cut s), ExactDecoder (M.cut c) (N.cut c)
      (q s) (tupleEncode (fun i => q (L.input c i))))
    {s : L.sorts} (p : Test L s) (x : M.State s) :
    holds N p (q s x) ↔ holds M p x := by
  induction p with
  | atom a => exact ha _ a x
  | neg p ih => exact not_congr (ih x)
  | conj p r ihp ihr => exact and_congr (ihp x) (ihr x)
  | step f p ih =>
    change holds N p (N.step f (q _ x)) ↔ holds M p (M.step f x)
    rw [hs]
    exact ih _
  | cut c p ih =>
    constructor
    · rintro ⟨ys, hys, htests⟩
      obtain ⟨zs, hzs, he⟩ := (hc _ c x ys).mp hys
      refine ⟨zs, hzs, ?_⟩
      intro i
      have hi := htests i
      rw [← congrFun he i] at hi
      exact (ih i (zs i)).mp hi
    · rintro ⟨zs, hzs, htests⟩
      refine ⟨tupleEncode (fun i => q (L.input c i)) zs,
        (hc _ c x _).mpr ⟨zs, hzs, rfl⟩, ?_⟩
      intro i
      exact (ih i (zs i)).mpr (htests i)

/-- Two binary relations can have the same two marginal images but different
whole joint records. Both examples expose every Boolean in each coordinate. -/
def Diagonal (p : Bool × Bool) : Prop := p.1 = p.2
def Antidiagonal (p : Bool × Bool) : Prop := p.1 ≠ p.2

theorem equal_marginals :
    (∀ b : Bool, (∃ c, Diagonal (b,c)) ↔ ∃ c, Antidiagonal (b,c)) ∧
    (∀ b : Bool, (∃ c, Diagonal (c,b)) ↔ ∃ c, Antidiagonal (c,b)) := by
  constructor <;> intro b <;> cases b <;> simp [Diagonal, Antidiagonal]

theorem unequal_joint_records : Diagonal ≠ Antidiagonal := by
  intro h
  have hd : Diagonal (false,false) := rfl
  have hn : ¬ Antidiagonal (false,false) := by simp [Antidiagonal]
  exact hn (h ▸ hd)

/-- Empty tuple feasibility is a relation bit, not automatically true. -/
theorem nullary_feasibility_distinguished :
    (∃ _y : Fin 0 → Bool, True) ∧ ¬ (∃ _y : Fin 0 → Bool, False) := by
  exact ⟨⟨Fin.elim0, trivial⟩, fun ⟨_, h⟩ => h⟩


/-- If a quotient identifies sources that differ on the feasibility of the
empty record, no source-fixed exact decoder exists. -/
theorem no_decoder_for_merged_nullary_feasibility :
    ¬ ∃ A : Unit → (Fin 0 → Bool) → Prop,
      ExactDecoder (fun (x : Bool) (_ : Fin 0 → Bool) => x = true)
        A (fun _ => ()) id := by
  rintro ⟨A, h⟩
  have ht : A () Fin.elim0 := (h true Fin.elim0).mpr ⟨Fin.elim0, rfl, rfl⟩
  obtain ⟨_, hf, _⟩ := (h false Fin.elim0).mp ht
  cases hf

/-- Cut exactness alone does not imply transport congruence: trivial cut rows
survive projection to the first Boolean, but swapping the coordinates does not. -/
theorem cut_exact_but_swap_does_not_descend :
    ExactDecoder (fun (_ : Bool × Bool) (_ : Unit) => True)
      (fun (_ : Bool) (_ : Unit) => True) Prod.fst id ∧
    ¬ Descends (Prod.fst : Bool × Bool → Bool) Prod.fst Prod.swap := by
  constructor
  · intro x u
    constructor
    · intro _
      exact ⟨u, trivial, rfl⟩
    · intro _
      trivial
  · rintro ⟨f, hf⟩
    have h0 := hf (false, false)
    have h1 := hf (false, true)
    have bad : (false : Bool) = true := h0.symm.trans h1
    cases bad

end JointQuotientDecoder
