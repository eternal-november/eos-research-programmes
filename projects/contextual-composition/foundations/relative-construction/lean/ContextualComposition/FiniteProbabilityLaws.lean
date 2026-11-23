module

public import ContextualComposition.ConeWiring
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Extensional finite-support probability on arbitrary sets. Weights are real, nonnegative, and sum to one. The pushforward is the genuine sum over fibres. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.FiniteProbabilityLaws

open CategoryTheory
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

structure Law (X : Type u) where
  mass : X →₀ ℝ
  nonnegative : 0 ≤ mass
  normalized : mass.sum (fun _ a => a) = 1

@[ext] theorem Law.ext {p q : Law X} (h : ∀ x, p.mass x = q.mass x) : p = q := by
  cases p; cases q; congr; exact DFunLike.ext _ _ h

def image (f : X → Y) (p : Law X) : Law Y where
  mass := p.mass.mapDomain f
  nonnegative := Finsupp.mapDomain_nonneg p.nonnegative
  normalized := (Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans p.normalized

def distribution : Type u ⥤ Type u where
  obj := Law
  map f := TypeCat.ofHom (image f)
  map_id _ := by
    apply ConcreteCategory.hom_ext; intro p
    exact Law.ext (fun x => DFunLike.congr_fun Finsupp.mapDomain_id x)
  map_comp f g := by
    apply ConcreteCategory.hom_ext; intro p
    exact Law.ext (fun x => DFunLike.congr_fun (Finsupp.mapDomain_fun_comp (v := p.mass) (fun a => f a) (fun b => g b)) x)

def expect (p : Law X) (h : X → ℝ) : ℝ := p.mass.sum (fun x a => a * h x)

theorem expect_congr (p : Law X) {h k : X → ℝ} (eq : ∀ x, h x = k x) : expect p h = expect p k :=
  congrArg (expect p) (funext eq)

theorem expect_add (p : Law X) (h k : X → ℝ) :
    expect p (fun x => h x + k x) = expect p h + expect p k := by
  simp [expect,Finsupp.sum,mul_add,Finset.sum_add_distrib]

theorem expect_image (p : Law X) (f : X → Y) (h : Y → ℝ) :
    expect (image f p) h = expect p (h ∘ f) :=
  Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def test (f : X → Bool) (x : X) : ℝ := if f x then 1 else 0

theorem point_as_test (p : Law X) (x : X) [DecidableEq X] :
    expect p (test (fun y => decide (y = x))) = p.mass x := by
  classical
  simp [expect,test,Finsupp.sum,Finset.sum_ite_eq',Finsupp.mem_support_iff]
  exact Eq.symm

theorem point_nonneg (p : Law X) (x : X) : 0 ≤ p.mass x := p.nonnegative x

theorem point_le_one (p : Law X) (x : X) : p.mass x ≤ 1 := by
  classical
  by_cases h : x ∈ p.mass.support
  · rw [← p.normalized]
    exact Finset.single_le_sum (f := fun x => p.mass x) (fun x _ => p.nonnegative x) h
  · simp [Finsupp.notMem_support_iff.mp h]

def ofFinite [Fintype X] (w : X → ℝ) (hn : ∀ x, 0 ≤ w x) (h : ∑ x, w x = 1) : Law X where
  mass := Finsupp.equivFunOnFinite.symm w
  nonnegative := hn
  normalized := (Finsupp.sum_fintype _ _ (fun _ => rfl)).trans h

theorem finite_expect [Fintype X] (p : Law X) (h : X → ℝ) :
    expect p h = ∑ x, p.mass x * h x := Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

def Interval := Set.Icc (0 : ℝ) 1
def bern (p : Interval) : Law Bool := ofFinite (fun i => if i then p.val else 1-p.val)
  (fun b => by cases b <;> simp [p.property.1,sub_nonneg.mpr p.property.2]) (by simp)

@[simp] theorem bern_true (p : Interval) : (bern p).mass true = p.val := rfl
@[simp] theorem bern_false (p : Interval) : (bern p).mass false = 1-p.val := rfl

theorem bool_determined (p q : Law Bool) (h : p.mass true = q.mass true) : p = q := by
  apply Law.ext; intro b; cases b
  · have s (r : Law Bool) : r.mass true + r.mass false = 1 := by
      have g : ∑ x : Bool, r.mass x = 1 := (Finsupp.sum_fintype r.mass (fun _ x => x) (fun _ => rfl)).symm.trans r.normalized
      simpa using g
    linarith [s p,s q]
  · exact h

theorem as_bern (p : Law Bool) : p = bern ⟨p.mass true,point_nonneg p _,point_le_one p _⟩ :=
  bool_determined p _ rfl

theorem push_test (p : Law X) (f : X → Bool) : (image f p).mass true = expect p (test f) := by
  rw [← point_as_test (image f p) true,expect_image]
  apply expect_congr; intro x; cases h : f x <;> simp [test,h]

theorem push_joint_test (p : Law (X × Y)) (f : X → Bool) (g : Y → Bool) :
    (image (Prod.map f g) p).mass (true,true) = expect p (test (fun z => f z.1 && g z.2)) := by
  rw [← point_as_test (image _ p) (true,true),expect_image]
  apply expect_congr; intro x; rcases x with ⟨x,y⟩
  cases hx : f x <;> cases hy : g y <;> simp [test,hx,hy]

@[simp] theorem image_id (p : Law X) : image id p = p :=
  Law.ext (fun x => DFunLike.congr_fun Finsupp.mapDomain_id x)

theorem image_comp (p : Law X) (f : X → Y) (g : Y → Z) : image g (image f p) = image (g ∘ f) p :=
  Law.ext (fun x => DFunLike.congr_fun (Finsupp.mapDomain_comp (f := f) (g := g) (v := p.mass)).symm x)

theorem expect_one (p : Law X) : expect p (fun _ => 1) = 1 := by
  simpa [expect] using p.normalized

inductive Three where | first | second | rest
deriving DecidableEq

def three (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) : Law Three where
  mass := Finsupp.single .first a + Finsupp.single .second b + Finsupp.single .rest (1-(a+b))
  nonnegative := add_nonneg (add_nonneg (Finsupp.single_nonneg.mpr ha) (Finsupp.single_nonneg.mpr hb))
    (Finsupp.single_nonneg.mpr (sub_nonneg.mpr hab))
  normalized := by
    simp only [Finsupp.sum_add_index' (h := fun (_ : Three) (r : ℝ) => r) (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (h := fun (_ : Three) (r : ℝ) => r) rfl]
    linarith

theorem expect_three (a b ha hb hab) (h : Three → ℝ) :
    expect (three a b ha hb hab) h = a*h .first + b*h .second + (1-(a+b))*h .rest := by
  simp only [expect,three,Finsupp.sum_add_index' (h := fun x (a : ℝ) => a * h x) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_single_index (h := fun x (a : ℝ) => a * h x) (zero_mul _)]

end ContextualComposition.FiniteProbabilityLaws
