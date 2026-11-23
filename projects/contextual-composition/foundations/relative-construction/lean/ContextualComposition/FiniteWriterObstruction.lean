module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! The two-object writer obstruction of the finite-contextad report §4. Kernels retain exactly their nonnegative real masses, summing to one in every row. -/

@[expose] public section

namespace ContextualComposition.FiniteWriterObstruction

inductive Obj where | one | bit

abbrev Carrier : Obj → Type
  | .one => Unit
  | .bit => Bool

instance (i : Obj) : Fintype (Carrier i) := by cases i <;> dsimp [Carrier] <;> infer_instance

instance (i : Obj) : DecidableEq (Carrier i) := by cases i <;> dsimp [Carrier] <;> infer_instance

variable {A B C D : Obj}

structure Kernel (A B : Obj) where
  mass : Carrier A → Carrier B → ℝ
  nonnegative : ∀ a b, 0 ≤ mass a b
  normalized : ∀ a, ∑ b, mass a b = 1

theorem Kernel.ext {p q : Kernel A B} (h : ∀ a b, p.mass a b = q.mass a b) : p = q := by
  cases p; cases q
  congr
  funext a b
  exact h a b

noncomputable def Kernel.comp (p : Kernel A B) (q : Kernel B C) : Kernel A C where
  mass a c := ∑ b, p.mass a b * q.mass b c
  nonnegative a c := by
    have nonneg (b : Carrier B) := mul_nonneg (p.nonnegative a b) (q.nonnegative b c)
    cases B with
    | one => simpa using nonneg ()
    | bit =>
      change 0 ≤ ∑ b : Bool, _
      simpa using add_nonneg (nonneg true) (nonneg false)
  normalized a := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, q.normalized, mul_one, p.normalized]

noncomputable def dirac (f : Carrier A → Carrier B) : Kernel A B where
  mass a b := if f a = b then 1 else 0
  nonnegative a b := by split <;> simp
  normalized a := by simp

noncomputable def fair : Kernel .one .bit where
  mass _ _ := 1 / 2
  nonnegative _ _ := by exact div_nonneg zero_le_one (by exact zero_le_two)
  normalized _ := by change (∑ _ : Bool, (1 : ℝ) / 2) = 1; simp

theorem flip_fair : fair.comp (dirac (A := .bit) (B := .bit) Bool.not) = fair := by
  apply Kernel.ext
  intro a b
  change (∑ i : Bool, (1 : ℝ) / 2 * (if Bool.not i = b then 1 else 0)) = 1 / 2
  cases b <;> simp

theorem unique_terminal (p : Kernel A .one) : p = dirac (B := .one) (fun _ => ()) := by
  apply Kernel.ext
  rintro a ⟨⟩
  have h := p.normalized a
  change (∑ i : Unit, p.mass a i) = 1 at h
  simpa [dirac] using h

/-- Literal product of a deterministic grade with an extensional normalized kernel. -/
structure Arrow (A B : Obj) where
  grade : Carrier A → Bool
  kernel : Kernel A B

noncomputable def writer (w : Carrier A → Bool) (f : Carrier A → Carrier B) : Arrow A B := ⟨w, dirac f⟩
def stochastic (p : Kernel A B) : Arrow A B := ⟨fun _ => false, p⟩

theorem terminal_writer (h : Arrow .one .one) : h = writer (B := .one) h.grade (fun _ => ()) := by
  cases h with
  | mk w k => exact congrArg (Arrow.mk w) (unique_terminal k)

/-- Execution-order composition, associativity, and composition preservation by the two specified inclusions. -/
structure Composition where
  comp : {A B C : Obj} → Arrow A B → Arrow B C → Arrow A C
  assoc : ∀ {A B C D : Obj} (p : Arrow A B) (q : Arrow B C) (r : Arrow C D),
    comp (comp p q) r = comp p (comp q r)
  kernels : ∀ {A B C : Obj} (p : Kernel A B) (q : Kernel B C),
    comp (stochastic p) (stochastic q) = stochastic (p.comp q)
  writers : ∀ {A B C : Obj} (w : Carrier A → Bool) (f : Carrier A → Carrier B)
    (v : Carrier B → Bool) (g : Carrier B → Carrier C),
    comp (writer w f) (writer v g) = writer (fun a => Bool.xor (w a) (v (f a))) (g ∘ f)

noncomputable def sample := stochastic fair
noncomputable def flipBit : Arrow .bit .bit := writer (fun _ => false) Bool.not
noncomputable def writeInput : Arrow .bit .one := writer id (fun _ => ())
noncomputable def toggle : Arrow .one .one := writer (fun _ => true) (fun _ => ())

theorem sample_flip (m : Composition) : m.comp sample flipBit = sample :=
  (m.kernels fair (dirac (A := .bit) (B := .bit) Bool.not)).trans (congrArg stochastic flip_fair)

theorem flip_write (m : Composition) : m.comp flipBit writeInput = m.comp writeInput toggle := by
  unfold flipBit writeInput toggle
  rw [m.writers, m.writers]
  congr 1
  funext b
  cases b <;> rfl

theorem no_toggle_fixed (m : Composition) (h : Arrow .one .one) : m.comp h toggle ≠ h := by
  intro eq
  have he : m.comp (writer (B := .one) h.grade (fun _ => ())) toggle = h := (congrArg (fun a => m.comp a toggle) (terminal_writer h)).symm.trans eq
  unfold toggle at he
  rw [m.writers] at he
  have bad := congrArg (fun x : Arrow .one .one => x.grade ()) he
  change Bool.xor (h.grade ()) true = h.grade () at bad
  cases e : h.grade () <;> simp [e] at bad

theorem no_associative_composition : ¬ Nonempty Composition := by
  rintro ⟨m⟩
  let h := m.comp sample writeInput
  apply no_toggle_fixed m h
  calc
    m.comp h toggle = m.comp sample (m.comp writeInput toggle) := m.assoc _ _ _
    _ = m.comp sample (m.comp flipBit writeInput) := congrArg _ (flip_write m).symm
    _ = m.comp (m.comp sample flipBit) writeInput := (m.assoc _ _ _).symm
    _ = h := congrArg (fun x => m.comp x writeInput) (sample_flip m)

end ContextualComposition.FiniteWriterObstruction
