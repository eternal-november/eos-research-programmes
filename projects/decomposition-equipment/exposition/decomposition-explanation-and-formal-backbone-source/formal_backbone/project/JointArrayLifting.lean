import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Source-fixed lifting of joint edge arrays. A path refers to shared edge IDs,
not independently chosen marginal factors. Empty paths are retained. -/
namespace JointArrayLifting
universe u v w
variable {D : Type u} {E : Type v} [Monoid D] [Monoid E]

def eval {A : Type w} (a : A → D) (p : List A) : D := (p.map a).prod

def Covered {A B : Type*} (path : B → List A) : Prop :=
  ∀ e, ∃ l, e ∈ path l

def FactorClosed (h : D →* E) : Prop :=
  ∀ a b, (∃ d, h d = a * b) → (∃ d, h d = a) ∧ (∃ d, h d = b)

def LiftAt {A B : Type*} (h : D →* E) (path : B → List A)
    (source : B → D) (target : A → E) : Prop :=
  ∃ a : A → D, (∀ e, h (a e) = target e) ∧ ∀ l, eval a (path l) = source l

@[simp] theorem eval_nil {A : Type*} (a : A → D) : eval a [] = 1 := rfl
@[simp] theorem eval_cons {A : Type*} (a : A → D) (e : A) (p : List A) :
    eval a (e :: p) = a e * eval a p := rfl

theorem map_eval {A : Type*} (h : D →* E) (a : A → D) (p : List A) :
    h (eval a p) = eval (fun e => h (a e)) p := by
  induction p with
  | nil => exact h.map_one
  | cons e p ih => simp only [eval_cons, h.map_mul, ih]

theorem eval_congr {A : Type*} {a b : A → D} (h : ∀ e, a e = b e) (p : List A) :
    eval a p = eval b p := by
  exact congrArg (fun f => eval f p) (funext h)

theorem image_factor {A : Type*} (h : D →* E) (fc : FactorClosed h)
    (a : A → E) (p : List A) (hp : ∃ d, h d = eval a p)
    (e : A) (he : e ∈ p) : ∃ d, h d = a e := by
  induction p with
  | nil => simp at he
  | cons x p ih =>
    obtain ⟨hx, ht⟩ := fc (a x) (eval a p) hp
    rcases List.mem_cons.mp he with hxe | he
    · subst e; exact hx
    · exact ih ht he

/-- Every edge is inverted once; all paths therefore use the same inverse for
shared parents. No independence or marginal matching assumption is used. -/
theorem unique_lift_of_injective_factorClosed {A B : Type*}
    (h : D →* E) (inj : Function.Injective h) (fc : FactorClosed h)
    (path : B → List A) (covered : Covered path)
    (source : B → D) (target : A → E)
    (valid : ∀ l, eval target (path l) = h (source l)) :
    ∃! a : A → D, (∀ e, h (a e) = target e) ∧ ∀ l, eval a (path l) = source l := by
  classical
  have image : ∀ e, ∃ d, h d = target e := by
    intro e
    obtain ⟨l, hl⟩ := covered e
    exact image_factor h fc target (path l) ⟨source l, (valid l).symm⟩ e hl
  let a : A → D := fun e => Classical.choose (image e)
  have ha : ∀ e, h (a e) = target e := fun e => Classical.choose_spec (image e)
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro l
    apply inj
    rw [map_eval, eval_congr ha, valid]
  · intro b hb
    funext e
    apply inj
    exact (hb.1 e).trans (ha e).symm

/-- All words, including intermediate products, are preserved. -/
theorem lift_intermediate_word {A : Type*} (h : D →* E)
    {a : A → D} {b : A → E} (lift : ∀ e, h (a e) = b e) (p : List A) :
    h (eval a p) = eval b p := (map_eval h a p).trans (eval_congr lift p)

/-- Any word-based contraction commutes with the uniquely lifted array. This
includes unit words [], and applies to retained intermediate certificates. -/
theorem unique_lift_natural {A B : Type*} (h : D →* E)
    (inj : Function.Injective h) (word : B → List A)
    {a : A → D} {b : A → E} (lift : ∀ e, h (a e) = b e)
    {c : B → D} (lift' : ∀ f, h (c f) = eval b (word f)) :
    c = fun f => eval a (word f) := by
  funext f
  apply inj
  exact (lift' f).trans (lift_intermediate_word h lift (word f)).symm

/-- Uniform finite-array property. A literal zero-edge one-leaf diagram is part
of the grammar; coverage for its empty edge type is vacuous. -/
def FullFiniteLifting (h : D →* E) : Prop :=
  ∀ n m (path : Fin m → List (Fin n)), Covered path →
    ∀ source target, (∀ l, eval target (path l) = h (source l)) →
      LiftAt h path source target

 theorem full_of_injective_factorClosed (h : D →* E)
    (inj : Function.Injective h) (fc : FactorClosed h) : FullFiniteLifting h := by
  intro n m path covered source target valid
  obtain ⟨a, ha, _⟩ := unique_lift_of_injective_factorClosed h inj fc path covered source target valid
  exact ⟨a, ha⟩

 theorem identity_reflection (h : D →* E) (full : FullFiniteLifting h)
    {x : D} (hx : h x = 1) : x = 1 := by
  let path : Fin 1 → List (Fin 0) := fun _ => []
  have cov : Covered path := fun e => Fin.elim0 e
  obtain ⟨a, _, ha⟩ := full 0 1 path cov (fun _ => x) (fun e => Fin.elim0 e)
    (fun _ => by simpa [path] using hx.symm)
  exact (ha 0).symm

 theorem factorClosed_of_full (h : D →* E) (full : FullFiniteLifting h) : FactorClosed h := by
  intro a b hab
  obtain ⟨x, hx⟩ := hab
  let path : Fin 1 → List (Fin 2) := fun _ => [0, 1]
  let target : Fin 2 → E := fun e => if e = 0 then a else b
  have cov : Covered path := by intro e; refine ⟨0, ?_⟩; fin_cases e <;> simp [path]
  obtain ⟨lift, hl, hs⟩ := full 2 1 path cov (fun _ => x) target
    (by intro l; simp [path, eval, target, hx])
  exact ⟨⟨lift 0, by simpa [target] using hl 0⟩, ⟨lift 1, by simpa [target] using hl 1⟩⟩

 theorem injective_of_full (h : D →* E) (full : FullFiniteLifting h) : Function.Injective h := by
  intro x y hxy
  let path : Fin 2 → List (Fin 3) := fun l => if l = 0 then [0, 1] else [0, 2]
  let source : Fin 2 → D := fun l => if l = 0 then x else y
  let target : Fin 3 → E := fun e => if e = 0 then h x else 1
  have cov : Covered path := by
    intro e
    fin_cases e
    · exact ⟨0, by simp [path]⟩
    · exact ⟨0, by simp [path]⟩
    · exact ⟨1, by simp [path]⟩
  have valid : ∀ l, eval target (path l) = h (source l) := by
    intro l; fin_cases l <;> simp [path, source, target, eval, hxy]
  obtain ⟨lift, hl, hs⟩ := full 3 2 path cov source target valid
  have h1 : lift 1 = 1 := identity_reflection h full (by simpa [target] using hl 1)
  have h2 : lift 2 = 1 := identity_reflection h full (by simpa [target] using hl 2)
  have hx : lift 0 = x := by simpa [path, source, eval, h1] using hs 0
  have hy : lift 0 = y := by simpa [path, source, eval, h2] using hs 1
  exact hx.symm.trans hy

 theorem full_iff (h : D →* E) :
    FullFiniteLifting h ↔ Function.Injective h ∧ FactorClosed h :=
  ⟨fun hf => ⟨injective_of_full h hf, factorClosed_of_full h hf⟩,
    fun hf => full_of_injective_factorClosed h hf.1 hf.2⟩

end JointArrayLifting
