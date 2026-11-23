module

public import ContextualComposition.NaturalMarginalCouplings
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! The normalized independent law supplies the natural marginal-only family. In the category of supplied effects and deterministic law-preserving maps, arbitrary cones can force incompatible joint laws. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.IndependentProbabilityProduct

open CategoryTheory CategoryTheory.Limits FiniteProbabilityLaws NaturalMarginalCouplings CouplingPullbacks AllCouplings CouplingChains ConeWiring
universe u v
variable {X : Type u} {Y : Type v}
set_option backward.isDefEq.respectTransparency false

def weights (p : Law X) (q : Law Y) : X × Y →₀ ℝ :=
  Finsupp.onFinset (p.mass.support ×ˢ q.mass.support) (fun z => p.mass z.1 * q.mass z.2) (by
    intro z h
    exact Finset.mem_product.mpr ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul h),
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h)⟩)

theorem support_weights (p : Law X) (q : Law Y) : (weights p q).support ⊆ p.mass.support ×ˢ q.mass.support :=
  Finsupp.support_onFinset_subset

def product (p : Law X) (q : Law Y) : Law (X × Y) where
  mass := weights p q
  nonnegative z := mul_nonneg (point_nonneg p z.1) (point_nonneg q z.2)
  normalized := by
    rw [Finsupp.sum_of_support_subset _ (support_weights p q) _ (fun _ _ => rfl),Finset.sum_product]
    change (∑ x ∈ p.mass.support, ∑ y ∈ q.mass.support, p.mass x * q.mass y) = 1
    have h : ∑ y ∈ q.mass.support, q.mass y = 1 := q.normalized
    simp only [← Finset.mul_sum,h,mul_one]
    exact p.normalized

theorem expect_product (p : Law X) (q : Law Y) (h : X × Y → ℝ) :
    expect (product p q) h = expect p (fun x => expect q (fun y => h (x,y))) := by
  change (weights p q).sum _ = _
  rw [Finsupp.sum_of_support_subset _ (support_weights p q) (fun z (a : ℝ) => a * h z) (fun _ _ => zero_mul _),Finset.sum_product]
  simp [expect,Finsupp.sum,weights,Finset.mul_sum,mul_assoc]

theorem expect_ext {p q : Law X} (h : ∀ f, expect p f = expect q f) : p = q := by
  classical
  apply Law.ext; intro x
  rw [← point_as_test p x,← point_as_test q x,h]

theorem expect_const (p : Law X) (c : ℝ) : expect p (fun _ => c) = c := by
  have t : ∑ x ∈ p.mass.support, p.mass x = 1 := p.normalized
  simp [expect,Finsupp.sum, ← Finset.sum_mul, t]

def family : Choice.{u} where
  couple := product
  fst p q := by
    apply expect_ext; intro h
    rw [expect_image,expect_product]
    exact expect_congr _ (fun x => expect_const q (h x))
  snd p q := by
    apply expect_ext; intro h
    rw [expect_image,expect_product]
    exact expect_const p (expect q h)
  natural f g p q := by
    apply expect_ext; intro h
    rw [expect_image,expect_product,expect_product,expect_image]
    exact expect_congr _ (fun x => (expect_image q g (fun y => h (f x,y))).symm)

theorem unique_family (rule : Choice.{u}) {A B : Type u} (p : Law A) (q : Law B) :
    rule.couple p q = product p q :=
  Law.ext (fun z => independence rule p q z.1 z.2)

variable {X Y : Type u} {F : Type u ⥤ Type u}

/-- One categorical product would fix a single joint pushforward through its two projections. -/
theorem no_product_of_distinct_couplings (P Q : Effect F) (a b : Hom F P Q) (different : a ≠ b) :
    ¬ HasBinaryProduct P Q := by
  intro hb
  let R := P ⨯ Q
  let fst : StateMap F R P := (prod.fst : P ⨯ Q ⟶ P)
  let snd : StateMap F R Q := (prod.snd : P ⨯ Q ⟶ Q)
  let both : R.carrier → P.carrier × Q.carrier := fun r => (fst.run r,snd.run r)
  have forced (t : Hom F P Q) : push F both R.law = t.val := by
    let W : Effect F := ⟨P.carrier × Q.carrier,t.val⟩
    let f : W ⟶ P := ⟨Prod.fst,t.property.1⟩
    let g : W ⟶ Q := ⟨Prod.snd,t.property.2⟩
    let m : W ⟶ R := prod.lift f g
    have first := congrArg (fun k : W ⟶ P => (show StateMap F W P from k).run) (prod.lift_fst f g)
    have second := congrArg (fun k : W ⟶ Q => (show StateMap F W Q from k).run) (prod.lift_snd f g)
    have sec : both ∘ (show StateMap F W R from m).run = id := by
      funext z; exact Prod.ext (congrFun first z) (congrFun second z)
    exact (congrArg (push F both) (show StateMap F W R from m).preserves).symm.trans
      ((push_push F _ _ t.val).trans ((congrArg (fun k => push F k t.val) sec).trans (push_id F _)))
  exact different (Subtype.ext ((forced a).symm.trans (forced b)))

def coin : Effect distribution.{0} := ⟨Bool,bern ⟨1/2,by norm_num,by norm_num⟩⟩

def independentCoin : Hom distribution coin coin :=
  ⟨product coin.law coin.law,family.fst _ _,family.snd _ _⟩

theorem independent_fails_product : ¬ HasBinaryProduct coin coin := by
  apply no_product_of_distinct_couplings coin coin independentCoin (identity distribution coin)
  intro eq
  have h := congrArg (fun r : Hom distribution coin coin => r.val) eq
  exact diagonal_forbidden family coin.law (x:=false) (y:=true)
    (by change 0 < 1 - (1:ℝ)/2; norm_num) (by change 0 < (1:ℝ)/2; norm_num) Bool.false_ne_true h

end ContextualComposition.IndependentProbabilityProduct
