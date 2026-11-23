module
public import ContextualComposition.RawOccurrenceLifting
public import ContextualComposition.OccurrenceFubiniPermutation
public import ContextualComposition.FiniteProbabilityMonad
public import ContextualComposition.NonemptyPossibilityMonad

/-! The joint prefix system, with its finite-distribution and nonempty-possibility realizations. The three assumptions play separate roles in admitting the root, interpreting a finite frontier independently of its chart, and forgetting its final layer. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.JointPrefixRealization
open CategoryTheory CouplingPullbacks TreeOverlapAdmission JointOccurrenceAdmission JointOccurrenceSystem
open GuardedOccurrencePrefixes RawOccurrenceLifting OccurrenceFubiniPermutation

universe u
variable {T : CategoryTheory.Monad (Type u)} {S : Polynomial.{u}} {V : Type u}

structure Hypotheses (T : CategoryTheory.Monad (Type u)) : Prop where
  weak : WeakPullbacks T.toFunctor
  affine : OccurrenceFubini.Affine T
  commutative : Commutative T

theorem probability : Hypotheses FiniteProbabilityMonad.monad.{u} :=
  ⟨FiniteProbabilityMonad.weak,FiniteProbabilityMonad.affine,
    (exchange_iff FiniteProbabilityMonad.monad.{u}).mp (@FiniteProbabilityMonad.exchange.{u})⟩

theorem possibility : Hypotheses NonemptyPossibilityMonad.monad.{u} :=
  ⟨NonemptyPossibilityMonad.weak,NonemptyPossibilityMonad.affine,
    (exchange_iff NonemptyPossibilityMonad.monad.{u}).mp (@NonemptyPossibilityMonad.exchange.{u})⟩

variable (H : Hypotheses T) (D : Diagram V) (A : ∀ v, System T.toFunctor S (D.space v))

def admittedChoices [Fintype V] (tree : D.graph.IsTree) (edges : ∀ x, BoundaryAgreement (atState D A x)) : Choices D A :=
  fun x => ((TreeOverlapAdmission.admission T.toFunctor (witnesses (atState D A x)) H.weak tree (atState D A x).effect).mp (edges x)).some

variable [Finitary S] (conn : D.graph.Connected) (q : Choices D A)

include H in
omit [Finitary S] in
theorem frontier_chart {P : Polynomial.{u}} [Finitary P] (raw : Body P (Raw D)) {n : Nat} (chart : P.Pos raw.1 ≃ Fin n) :
    sample (jointSystem D A conn q) raw = productBy T chart (fun i => (jointSystem D A conn q).effect (raw.2 i)) :=
  frontier_product_eq T ((exchange_iff T).mpr H.commutative) chart _

include H in
theorem joint_native_prefix_system (v : V) (x : Raw D) (n : Nat) :
    let J := jointSystem D A conn q
    let h := coord D v
    let m := componentMap D A conn q v
    push T.toFunctor (prefixMap m x n).run (prefixes J x n).law = (prefixes (A v) (h x) n).law ∧
    (∀ t, map (power S n) h ((prefixes J x n).frontier t) = (prefixes (A v) (h x) n).frontier ((prefixMap m x n).run t)) ∧
    push T.toFunctor (forgetLast J x n) (prefixes J x (n+1)).law = (prefixes J x n).law ∧
    (∀ t, (prefixMap m x n).run (forgetLast J x n t) = forgetLast (A v) (h x) n ((prefixMap m x (n+1)).run t)) :=
  ⟨(jointPrefixMap D A conn q v x n).marginal,(jointPrefixMap D A conn q v x n).body,
    prefix_truncate H.affine _ _ _,truncate_map _ _ _⟩

theorem joint_raw_lifting (v : V) (x : Raw D)
    (onto : ∀ y, Reachable (jointSystem D A conn q) x y → Function.Surjective ((componentMap D A conn q v).onWitness y)) :
    Function.Surjective (mapLimit (componentMap D A conn q v) x) :=
  raw_limit_surjective _ _ onto

end ContextualComposition.JointPrefixRealization
