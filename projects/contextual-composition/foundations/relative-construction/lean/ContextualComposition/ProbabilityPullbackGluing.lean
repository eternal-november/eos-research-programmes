module

public import ContextualComposition.IndependentProbabilityProduct
public import Mathlib.Tactic.FieldSimp

/-! The finite-support distribution functor weakly preserves all Set pullbacks. Zero-mass boundary fibres and unmatched raw input states contribute zero. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.ProbabilityPullbackGluing

open FiniteProbabilityLaws CouplingPullbacks IndependentProbabilityProduct
universe u
variable {X Y S : Type u} (f : X → S) (g : Y → S) (p : Law X) (q : Law Y)

theorem fibre [DecidableEq S] (s : S) :
    (image f p).mass s = ∑ x ∈ p.mass.support, if f x = s then p.mass x else 0 := by
  classical
  simp [image,Finsupp.mapDomain_apply,Finsupp.single_apply,Finsupp.sum]

theorem le_boundary (x : X) : p.mass x ≤ (image f p).mass (f x) := by
  classical
  rw [fibre]
  by_cases hx : x ∈ p.mass.support
  · have h := Finset.single_le_sum (f := fun i => if f i = f x then p.mass i else 0)
      (s := p.mass.support) (fun i _ => by split <;> first | exact point_nonneg p i | exact le_rfl) hx
    simpa using h
  · rw [Finsupp.notMem_support_iff.mp hx]
    exact Finset.sum_nonneg (fun i _ => by split <;> first | exact point_nonneg p i | exact le_rfl)

/-- Mass of one pair before restriction to the full raw pullback. Division by zero in the zero-mass case evaluates to zero. -/
def cell (z : X × Y) : ℝ := by
  classical
  exact if f z.1 = g z.2 then p.mass z.1 * q.mass z.2 / (image f p).mass (f z.1) else 0

theorem cell_nonneg (z : X × Y) : 0 ≤ cell f g p q z := by
  classical
  unfold cell; split
  · exact div_nonneg (mul_nonneg (point_nonneg _ _) (point_nonneg _ _)) (point_nonneg _ _)
  · exact le_rfl

theorem row_total (same : image f p = image g q) (x : X) :
    ∑ y ∈ q.mass.support, cell f g p q (x,y) = p.mass x := by
  classical
  let m := (image f p).mass (f x)
  have eq : ∑ y ∈ q.mass.support, (if g y = f x then q.mass y else 0) = m := by
    rw [← fibre,← same]
  have point (y : Y) : cell f g p q (x,y) = (p.mass x / m) * (if g y = f x then q.mass y else 0) := by
    by_cases h : f x = g y
    · change (if f x = g y then _ else _) = _
      rw [ite_eq_left h,ite_eq_left h.symm]
      dsimp [m]; ring
    · simp [cell,h,Ne.symm h]
  simp_rw [point]; rw [← Finset.mul_sum,eq]
  by_cases h : m = 0
  · have hx : p.mass x ≤ m := le_boundary f p x
    rw [h] at hx ⊢
    simp [le_antisymm hx (point_nonneg p x)]
  · field_simp

theorem col_total (same : image f p = image g q) (y : Y) :
    ∑ x ∈ p.mass.support, cell f g p q (x,y) = q.mass y := by
  classical
  rw [← row_total g f q p same.symm y]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = g y
  · change (if f x = g y then _ else _) = (if g y = f x then _ else _)
    rw [ite_eq_left h,ite_eq_left h.symm,same,h,mul_comm (p.mass x) (q.mass y)]
  · simp [cell,h,Ne.symm h]

def pairWeights : X × Y →₀ ℝ := Finsupp.onFinset (p.mass.support ×ˢ q.mass.support) (cell f g p q) (by
  classical
  rintro ⟨x,y⟩ h
  refine Finset.mem_product.mpr ⟨Finsupp.mem_support_iff.mpr ?_,Finsupp.mem_support_iff.mpr ?_⟩
  · intro hz; exact h (by simp [cell,hz])
  · intro hz; exact h (by simp [cell,hz]))

theorem sum_weights {N : Type*} [AddCommMonoid N] (h : X × Y → ℝ → N) (hz : ∀ z, h z 0 = 0) :
    (pairWeights f g p q).sum h = ∑ x ∈ p.mass.support, ∑ y ∈ q.mass.support, h (x,y) (cell f g p q (x,y)) := by
  classical
  have hs : (pairWeights f g p q).support ⊆ p.mass.support ×ˢ q.mass.support := Finsupp.support_onFinset_subset
  exact (Finsupp.sum_of_support_subset _ hs h (fun z _ => hz z)).trans (Finset.sum_product _ _ _)

def joint (same : image f p = image g q) : Law (X × Y) where
  mass := pairWeights f g p q
  nonnegative := cell_nonneg f g p q
  normalized := by
    rw [sum_weights _ _ _ _ _ (fun _ => rfl)]
    simp_rw [row_total f g p q same]
    exact p.normalized

theorem left_joint (same : image f p = image g q) : image Prod.fst (joint f g p q same) = p := by
  apply expect_ext; intro h
  rw [expect_image]
  change (pairWeights f g p q).sum (fun z a => a * h z.1) = _
  rw [sum_weights _ _ _ _ (fun z a => a * h z.1) (fun _ => zero_mul _)]
  simp_rw [← Finset.sum_mul,row_total f g p q same]
  rfl

theorem right_joint (same : image f p = image g q) : image Prod.snd (joint f g p q same) = q := by
  apply expect_ext; intro h
  rw [expect_image]
  change (pairWeights f g p q).sum (fun z a => a * h z.2) = _
  rw [sum_weights _ _ _ _ (fun z a => a * h z.2) (fun _ => zero_mul _),Finset.sum_comm]
  simp_rw [← Finset.sum_mul,col_total f g p q same]
  rfl

theorem on_pullback (same : image f p = image g q) :
    ∃ l : Law (PB f g), image Subtype.val l = joint f g p q same := by
  classical
  let t := joint f g p q same
  have match_on (z : X × Y) (hz : z ∈ t.mass.support) : f z.1 = g z.2 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hz) (show cell f g p q z = 0 by simp [cell,h])
  have exists_match : Nonempty (PB f g) := by
    by_contra! he
    have zero : t.mass = 0 := by
      ext z; by_contra hn
      exact he.false ⟨z,match_on z (Finsupp.mem_support_iff.mpr hn)⟩
    have n := t.normalized
    rw [zero] at n
    simp at n
  let restore (z : X × Y) : PB f g := if h : f z.1 = g z.2 then ⟨z,h⟩ else exists_match.some
  refine ⟨image restore t,?_⟩
  rw [image_comp]
  apply Law.ext; intro z
  have e : t.mass.mapDomain (Subtype.val ∘ restore) = t.mass.mapDomain id :=
    Finsupp.mapDomain_congr (fun w hw => by simp [restore,match_on w hw])
  exact DFunLike.congr_fun (e.trans Finsupp.mapDomain_id) z

/-- The canonical comparison is surjective; the law is on all matched pairs, including raw pairs with zero weight. -/
theorem weak : WeakPullbacks distribution.{u} := by
  intro X Y S f g m
  obtain ⟨⟨p,q⟩,same⟩ := m
  change image f p = image g q at same
  obtain ⟨t,ht⟩ := on_pullback f g p q same
  refine ⟨t,Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact (image_comp t Subtype.val Prod.fst).symm.trans ((congrArg (image Prod.fst) ht).trans (left_joint _ _ _ _ same))
  · exact (image_comp t Subtype.val Prod.snd).symm.trans ((congrArg (image Prod.snd) ht).trans (right_joint _ _ _ _ same))

end ContextualComposition.ProbabilityPullbackGluing
