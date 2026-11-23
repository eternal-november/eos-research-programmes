module

public import ContextualComposition.TreeOverlapBoundaries
public import ContextualComposition.FiniteProbabilityMonad

/-! The finite distribution realizations of strict hiding, three cyclic fair-bit constraints and a zero-weight dead raw witness. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.ProbabilityOverlapBoundaries

open CategoryTheory FiniteProbabilityLaws FiniteProbabilityMonad IndependentProbabilityProduct CouplingPullbacks AllCouplings CouplingChains TreeOverlapAdmission TreeOverlapBoundaries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def point : Effect distribution.{0} := ⟨Unit,dirac ()⟩
def keep : StateMap distribution coin coin := ⟨id,push_id _ _⟩
def hide : StateMap distribution coin point where
  run := fun _ => ()
  preserves := by
    apply expect_ext; intro h
    change expect (image (fun _ : Bool => ()) coin.law) h = expect (dirac ()) h
    rw [expect_image,expect_dirac]
    exact expect_const coin.law _

/-- After erasing the middle bit, every full fair-bit endpoint coupling becomes a possible composite. -/
theorem hidden_all (e : Hom distribution coin coin) :
    compose distribution (change distribution keep hide (identity distribution coin))
      (change distribution hide keep (identity distribution coin)) (change distribution keep keep e) := by
  let triple (z : Bool × Bool) := (z.1,(),z.2)
  refine ⟨push distribution triple e.val,?_,?_,?_⟩
  · change push distribution xy (push distribution triple e.val) = push distribution _ (push distribution diag coin.law)
    rw [push_push,push_push]
    let tag := fun x : Bool => (x,())
    exact (push_push distribution Prod.fst tag e.val).symm.trans (congrArg (push distribution tag) e.property.1)
  · change push distribution yz (push distribution triple e.val) = push distribution _ (push distribution diag coin.law)
    rw [push_push,push_push]
    let tag := fun x : Bool => ((),x)
    exact (push_push distribution Prod.snd tag e.val).symm.trans (congrArg (push distribution tag) e.property.2)
  · exact push_push distribution triple xz e.val

theorem strict_hiding :
    ¬ compose distribution (identity distribution coin) (identity distribution coin) independentCoin ∧
    compose distribution (change distribution keep hide (identity distribution coin))
      (change distribution hide keep (identity distribution coin)) (change distribution keep keep independentCoin) := by
  refine ⟨?_,hidden_all _⟩
  intro h
  have eq := (left_unit distribution ProbabilityPullbackGluing.weak (identity distribution coin) independentCoin).mp h
  exact NaturalMarginalCouplings.diagonal_forbidden family coin.law (x:=false) (y:=true)
    (by change 0 < 1 - (1:ℝ)/2; norm_num) (by change 0 < (1:ℝ)/2; norm_num) Bool.false_ne_true (congrArg Subtype.val eq.symm)

private theorem cycle_leg (i j : Vertex) : image (cycleLeg i j) coin.law = coin.law := by
  cases i <;> cases j <;> try exact image_id _
  apply bool_determined
  rw [push_test, finite_expect]
  change (∑ x : Bool, (coin.law.mass x) * test Bool.not x) = _
  simp [coin,test]
  norm_num

theorem cycle_agreement : Compatible distribution cycle (fun _ => coin.law) :=
  fun {i j} _ => (cycle_leg i j).trans (cycle_leg j i).symm

theorem cycle_no_distribution : ¬ Nonempty (Joint distribution cycle (fun _ => coin.law)) := by
  rintro ⟨q⟩
  have hz : q.val.mass = 0 := by ext x; exact False.elim (cycle_empty x)
  have n := q.val.normalized
  rw [hz] at n; simp at n

theorem zero_weight_dead :
    Nonempty (Joint distribution dead (fun _ => dirac false)) ∧ ¬ Function.Surjective (coord dead false) := by
  refine ⟨⟨dirac deadTuple,?_⟩,dead_projection⟩
  intro i
  exact DependentConeInterchange.push_ret monad deadTuple (coord dead i)

end ContextualComposition.ProbabilityOverlapBoundaries
