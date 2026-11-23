module

public import ContextualComposition.IndependentProbabilityProduct
public import Mathlib.Data.Fintype.Prod

/-! An interval of distinct indexed joint laws for the same two finite fair-bit marginals. -/

@[expose] public section
namespace ContextualComposition.FairBitCouplingFamily

open FiniteProbabilityLaws IndependentProbabilityProduct AllCouplings
noncomputable section

private theorem sum_pair (h : Bool × Bool → ℝ) : (∑ z, h z) = (h (true,true) + h (true,false)) + (h (false,true) + h (false,false)) := by
  change ∑ z ∈ Finset.univ ×ˢ Finset.univ, h z = _
  rw [Finset.sum_product]; simp

def table (t : Interval) : Law (Bool × Bool) := ofFinite
  (fun p => if p.1 = p.2 then t.val/2 else (1-t.val)/2)
  (fun _ => by split <;> linarith [t.property.1,t.property.2])
  (by rw [sum_pair]; simp; ring)

theorem table_marginal (t : Interval) :
    image Prod.fst (table t) = coin.law ∧ image Prod.snd (table t) = coin.law := by
  constructor <;> apply bool_determined <;> rw [push_test,finite_expect,sum_pair] <;>
    simp [test,table,ofFinite,coin,bern] <;> ring

def coupling (t : Interval) : Hom distribution coin coin := ⟨table t,table_marginal t⟩

theorem coupled_interval : Function.Injective coupling := by
  intro t r e
  have h := congrArg (fun a : Hom distribution coin coin => a.val.mass (true,true)) e
  change t.val / 2 = r.val / 2 at h
  exact Subtype.ext (by linarith)

end
end ContextualComposition.FairBitCouplingFamily
