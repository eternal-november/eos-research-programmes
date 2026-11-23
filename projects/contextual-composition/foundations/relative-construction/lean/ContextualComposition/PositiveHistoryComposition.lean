module
public import ContextualComposition.PositiveHistoryReflection
public import ContextualComposition.FiniteProbabilityMonad
public import Mathlib.Data.Fintype.BigOperators

/-! Sequential positive finite histories and the actual comparison of
support samplers. Each execution retains the first and second witness. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.PositiveHistoryComposition
open CategoryTheory FiniteProbabilityLaws FiniteProbabilityMonad PositiveHistoryReflection IndependentProbabilityProduct
universe u
set_option backward.isDefEq.respectTransparency false
variable {A B C D X : Type u}

def dependentLaw (p : Law X) (Y : X → Type u) (q : ∀ x, Law (Y x)) [Finite X] [∀ x, Finite (Y x)] :
    Law (Σ x, Y x) := by
  classical
  let _ := Fintype.ofFinite X
  let _ := fun x => Fintype.ofFinite (Y x)
  refine ofFinite (fun z : Σ x, Y x => p.mass z.1 * (q z.1).mass z.2)
    (fun z => mul_nonneg (point_nonneg _ _) (point_nonneg _ _)) ?_
  rw [Fintype.sum_sigma]
  simp_rw [← Finset.mul_sum]
  have norm {Z : Type u} [Fintype Z] (m : Law Z) : ∑ z, m.mass z = 1 :=
    (Finsupp.sum_fintype _ _ (fun _ => rfl)).symm.trans m.normalized
  simp [norm]

theorem dependent_mass (p : Law X) (Y : X → Type u) (q : ∀ x, Law (Y x)) [Finite X] [∀ x, Finite (Y x)] (z : Σ x, Y x) :
    (dependentLaw p Y q).mass z = p.mass z.1 * (q z.1).mass z.2 := rfl

theorem dependent_expect (p : Law X) (Y : X → Type u) (q : ∀ x, Law (Y x)) [Finite X] [∀ x, Finite (Y x)]
    (f : (Σ x, Y x) → ℝ) :
    expect (dependentLaw p Y q) f = expect p (fun x => expect (q x) (fun y => f ⟨x,y⟩)) := by
  classical
  let _ := Fintype.ofFinite X
  let _ := fun x => Fintype.ofFinite (Y x)
  simp_rw [finite_expect]
  rw [Fintype.sum_sigma]
  simp [dependent_mass,mul_assoc,Finset.mul_sum]

def serial (P : History A B) (Q : History B C) : History A C := by
  let _ := P.finite
  let _ := Q.finite
  refine {
    witness := fun a => Σ (x : P.witness a), Q.witness (P.output a x)
    finite := fun a => by
      let _ := Fintype.ofFinite (P.witness a)
      let _ (x : P.witness a) := Fintype.ofFinite (Q.witness (P.output a x))
      exact Finite.of_fintype _
    weights := fun a => dependentLaw (P.weights a) _ (fun x => Q.weights (P.output a x))
    output := fun a z => Q.output (P.output a z.1) z.2 }

theorem kernel_serial (P : History A B) (Q : History B C) (a : A) :
    kernel (serial P Q) a = mixture (kernel P a) (kernel Q) := by
  let _ := P.finite
  let _ := Q.finite
  apply expect_ext
  intro h
  change expect (image (fun z : Σ x : P.witness a, Q.witness (P.output a x) => Q.output _ z.2)
    (dependentLaw (P.weights a) _ (fun x => Q.weights (P.output a x)))) h = _
  rw [expect_image,dependent_expect,expect_mixture]
  change _ = expect (image (P.output a) (P.weights a)) _
  rw [expect_image]
  apply expect_congr
  intro x
  exact (expect_image (Q.weights _) (Q.output _) h).symm

def compose (P : Positive A B) (Q : Positive B C) : Positive A C where
  history := serial P.history Q.history
  positive a z := mul_pos (P.positive a z.1) (Q.positive _ z.2)

def kernelComp (k : A → Law B) (l : B → Law C) : A → Law C := fun a => mixture (k a) l

/-- The unique comparison to the sampler of the composed kernel. -/
def samplerComparison (k : A → Law B) (l : B → Law C) : compose (support k) (support l) ⟶ support (kernelComp k l) :=
  toSupport _ _ (by
    funext a
    exact (kernel_serial _ _ a).trans (congrArg₂ mixture (congrFun (kernel_support k) a) (kernel_support l)))

theorem comparison_output (k : A → Law B) (l : B → Law C) (a : A)
    (z : Σ x : Supported (k a), Supported (l x.val)) :
    ((samplerComparison k l).run a z).val = z.2.val := (samplerComparison k l).output a z

def uniform : Law Bool := bern ⟨1/2,by norm_num,by norm_num⟩

theorem uniform_mem (b : Bool) : b ∈ uniform.mass.support := by
  apply Finsupp.mem_support_iff.mpr
  cases b <;> norm_num [uniform]

def point : Supported (dirac ()) := ⟨(),by simp [dirac]⟩

/-- After a fair intermediate bit and a constant continuation there are
two distinct histories with the same returned output. -/
theorem comparison_not_injective :
    ¬ Function.Injective ((samplerComparison (fun _ : Unit => uniform) (fun _ => dirac ())).run ()) := by
  intro h
  let x : Supported uniform := ⟨false,uniform_mem false⟩
  let y : Supported uniform := ⟨true,uniform_mem true⟩
  have same := h (show (samplerComparison (fun _ : Unit => uniform) (fun _ => dirac ())).run () ⟨x,point⟩ =
      (samplerComparison (fun _ : Unit => uniform) (fun _ => dirac ())).run () ⟨y,point⟩ from Subtype.ext rfl)
  exact Bool.noConfusion (congrArg (fun t : Σ _ : Supported uniform, Supported (dirac ()) => t.1.val) same)

theorem comparison_not_iso : ¬ IsIso (samplerComparison (fun _ : Unit => uniform) (fun _ => dirac ())) := by
  intro h
  let f := samplerComparison (fun _ : Unit => uniform) (fun _ => dirac ())
  apply comparison_not_injective
  intro x y eq
  let g := CategoryTheory.inv f
  have left (z) : g.run () (f.run () z) = z :=
    congrArg (fun k : compose (support (fun _ : Unit => uniform)) (support (fun _ => dirac ())) ⟶ _ => k.run () z) (IsIso.hom_inv_id f)
  exact (left x).symm.trans ((congrArg (g.run ()) eq).trans (left y))

def coinExperiment : Positive Unit Unit where
  history := ⟨fun _ => Bool,fun _ => inferInstance,fun _ => uniform,fun _ _ => ()⟩
  positive _ b := lt_of_le_of_ne (point_nonneg uniform b) (Finsupp.mem_support_iff.mp (uniform_mem b)).symm

theorem flip_preserves : image Bool.not uniform = uniform := by
  apply bool_determined
  rw [push_test,finite_expect]
  change (∑ b : Bool, uniform.mass b * test Bool.not b) = _
  norm_num [test,uniform]

def flipCell : coinExperiment ⟶ coinExperiment :=
  ⟨fun _ => Bool.not,fun _ => flip_preserves,fun _ _ => rfl⟩

theorem law_nonfaithful : ¬ (evaluate (A := Unit) (B := Unit)).Faithful := by
  intro f
  have h : flipCell = 𝟙 coinExperiment := f.map_injective (Subsingleton.elim _ _)
  exact Bool.noConfusion (congrArg (fun t : coinExperiment ⟶ coinExperiment => t.run () false) h)

/-- A raw zero-mass output may fall outside the support of the pushed
law. The support-sampler unit from the positive category then fails. -/
def zeroExperiment : History Unit Bool :=
  ⟨fun _ => Bool,fun _ => inferInstance,fun _ => dirac false,fun _ => id⟩

theorem raw_support_obstruction :
    ¬ Nonempty (Map zeroExperiment (support (kernel zeroExperiment)).history) := by
  rintro ⟨f⟩
  let x := f.run () true
  have he : x.val = true := f.output () true
  have hx : x.val ∈ (dirac false).mass.support := by simpa [kernel,zeroExperiment] using x.property
  rw [he] at hx
  simp [dirac] at hx

end ContextualComposition.PositiveHistoryComposition
