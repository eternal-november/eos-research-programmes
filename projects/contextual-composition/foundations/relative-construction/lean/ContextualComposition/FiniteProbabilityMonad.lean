module

public import ContextualComposition.ProbabilityPullbackGluing
public import ContextualComposition.DependentConeInterchange
public import Mathlib.Data.Finsupp.SMul

/-! The weakly pullback-preserving finite-support functor equipped with its actual commutative affine mixture monad. These laws instantiate the finite-frontier assumptions without any claim about infinite effects. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.FiniteProbabilityMonad

open CategoryTheory FiniteProbabilityLaws IndependentProbabilityProduct CouplingPullbacks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Type u}

def dirac (x : X) : Law X where
  mass := Finsupp.single x 1
  nonnegative := Finsupp.single_nonneg.mpr zero_le_one
  normalized := Finsupp.sum_single_index rfl

theorem expect_dirac (x : X) (h : X → ℝ) : expect (dirac x) h = h x :=
  (Finsupp.sum_single_index (h := fun x (w:ℝ) => w * h x) (zero_mul _)).trans (one_mul _)

def mixtureWeights (p : Law X) (k : X → Law Y) : Y →₀ ℝ :=
  p.mass.sum (fun x a => a • (k x).mass)

private theorem weighted (p : Law X) (k : X → Law Y) (f : Y → ℝ) :
    (mixtureWeights p k).sum (fun y a => a * f y) = expect p (fun x => expect (k x) f) := by
  unfold mixtureWeights
  rw [Finsupp.sum_sum_index (h := fun y (a:ℝ) => a * f y) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  change _ = p.mass.sum _
  apply Finsupp.sum_congr
  intro x _
  rw [Finsupp.sum_smul_index (h := fun y (a:ℝ) => a * f y) (fun _ => zero_mul _)]
  simp [expect,Finsupp.sum,Finset.mul_sum,mul_assoc]

def mixture (p : Law X) (k : X → Law Y) : Law Y where
  mass := mixtureWeights p k
  nonnegative := by
    intro y
    change 0 ≤ (∑ x ∈ p.mass.support, p.mass x • (k x).mass) y
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonnegative x) ((k x).nonnegative y))
  normalized := by
    simpa only [mul_one,expect_one] using weighted p k (fun _ => 1)

theorem expect_mixture (p : Law X) (k : X → Law Y) (h : Y → ℝ) :
    expect (mixture p k) h = expect p (fun x => expect (k x) h) := weighted p k h

def monad : CategoryTheory.Monad (Type u) where
  toFunctor := distribution
  η := {
    app := fun _ => TypeCat.ofHom dirac
    naturality := by
      intro A B f; apply ConcreteCategory.hom_ext; intro a
      apply expect_ext; intro h
      change expect (dirac (f a)) h = expect (image f (dirac a)) h
      rw [expect_image,expect_dirac,expect_dirac]; rfl }
  μ := {
    app := fun _ => TypeCat.ofHom (fun p => mixture p id)
    naturality := by
      intro A B f; apply ConcreteCategory.hom_ext; intro p
      change Law (Law A) at p
      apply expect_ext; intro h
      change expect (mixture (image (image f) p) id) h = expect (image f (mixture p id)) h
      simp only [expect_mixture,expect_image]
      apply expect_congr; intro x; exact expect_image x f h }
  assoc A := by
    apply ConcreteCategory.hom_ext; intro p; apply expect_ext; intro h
    change expect (mixture (image (fun q => mixture q id) p) id) h = expect (mixture (mixture p id) id) h
    simp only [expect_mixture,expect_image]
    exact expect_congr p (fun x => expect_mixture x id h)
  left_unit A := by
    apply ConcreteCategory.hom_ext; intro p; apply expect_ext; intro h
    change expect (mixture (dirac p) id) h = _
    rw [expect_mixture,expect_dirac]; rfl
  right_unit A := by
    apply ConcreteCategory.hom_ext; intro p; apply expect_ext; intro h
    change expect (mixture (image dirac p) id) h = _
    rw [expect_mixture,expect_image]
    exact expect_congr p (fun x => expect_dirac x h)

theorem bind_eq (p : Law X) (k : X → Law Y) :
    DependentConeInterchange.bind monad p k = mixture p k := by
  apply expect_ext; intro h
  change expect (mixture (image k p) id) h = _
  simp only [expect_mixture,expect_image]; rfl

theorem affine : Subsingleton (monad.obj PUnit.{u+1}) where
  allEq p q := expect_ext (fun f => by
    have hf : f = fun _ => f PUnit.unit := funext fun ⟨⟩ => rfl
    exact (congrArg (expect p) hf).trans ((expect_const p _).trans ((expect_const q _).symm.trans (congrArg (expect q) hf).symm)))

theorem exchange (p : Law X) (q : Law Y) (k : X → Y → Law Z) :
    DependentConeInterchange.bind monad p (fun x => DependentConeInterchange.bind monad q (k x)) =
    DependentConeInterchange.bind monad q (fun y => DependentConeInterchange.bind monad p (fun x => k x y)) := by
  apply expect_ext; intro h
  simp only [bind_eq,expect_mixture]
  let f (x : X) (y : Y) := expect (k x y) h
  change expect p (fun x => expect q (f x)) = expect q (fun y => expect p (fun x => f x y))
  simp only [expect,Finsupp.sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact mul_left_comm _ _ _

theorem weak : WeakPullbacks monad.toFunctor := ProbabilityPullbackGluing.weak

end ContextualComposition.FiniteProbabilityMonad
