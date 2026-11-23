module
public import ContextualComposition.DependentConeInterchange
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fin.Tuple.Basic

/-! The ordered finite Fubini product used on a common addressed frontier. The implementation uses the monad's unit and bind, with one enumeration for each position set. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.OccurrenceFubini
open CategoryTheory CouplingPullbacks DependentConeInterchange
universe u
variable (T : CategoryTheory.Monad (Type u))

def productFin : (n : Nat) → {A : Fin n → Type u} → (∀ i, T.obj (A i)) → T.obj (∀ i, A i)
  | 0, _, _ => ret T (fun i => nomatch i)
  | n+1, _, p => bind T (p 0) (fun x => push T.toFunctor (Fin.cons x) (productFin n (fun i => p i.succ)))

theorem productFin_natural (n : Nat) {A B : Fin n → Type u} (p : ∀ i, T.obj (A i)) (f : ∀ i, A i → B i) :
    push T.toFunctor (fun x i => f i (x i)) (productFin T n p) = productFin T n (fun i => push T.toFunctor (f i) (p i)) := by
  induction n with
  | zero =>
    simp only [productFin,push_ret]
    apply congrArg (ret T)
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [productFin,push_bind,bind_push]
    apply congrArg (bind T (p 0))
    funext x
    change push T.toFunctor _ (push T.toFunctor (Fin.cons x) _) = push T.toFunctor (Fin.cons (f 0 x)) _
    rw [← ih (fun i => p i.succ) (fun i => f i.succ),push_push,push_push]
    apply congrArg (fun k => push T.toFunctor k _)
    funext t i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- The tuple type still uses the original positions. Only sequencing the independent effects uses their finite chart. -/
def product {I : Type u} [Finite I] {A : I → Type u} (p : ∀ i, T.obj (A i)) : T.obj (∀ i, A i) :=
  letI := Fintype.ofFinite I
  let e := Fintype.equivFin I
  push T.toFunctor (Equiv.piCongrLeft' A e).symm (productFin T _ (fun i => p (e.symm i)))

theorem product_natural {I : Type u} [Finite I] {A B : I → Type u} (p : ∀ i, T.obj (A i)) (f : ∀ i, A i → B i) :
    push T.toFunctor (fun x i => f i (x i)) (product T p) = product T (fun i => push T.toFunctor (f i) (p i)) := by
  classical
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let a := Equiv.piCongrLeft' A e
  let b := Equiv.piCongrLeft' B e
  change push T.toFunctor _ (push T.toFunctor a.symm _) = push T.toFunctor b.symm _
  rw [← productFin_natural T _ (fun i => p (e.symm i)) (fun i => f (e.symm i)),push_push,push_push]
  apply congrArg (fun k => push T.toFunctor k _)
  funext t
  apply b.injective
  funext i
  change f (e.symm i) ((a (a.symm t)) i) = (b (b.symm (fun j => f (e.symm j) (t j)))) i
  simp

/-- Affinity only enters the layer-truncation proof. -/
def Affine := Subsingleton (T.obj PUnit.{u+1})

theorem discard (aff : Affine T) {A B : Type u} (p : T.obj A) (b : B) :
    push T.toFunctor (fun _ => b) p = ret T b := by
  let f : A → PUnit.{u+1} := fun _ => ⟨⟩
  let g : PUnit.{u+1} → B := fun _ => b
  have h : push T.toFunctor f p = ret T PUnit.unit := aff.allEq _ _
  exact (push_push T.toFunctor f g p).symm.trans ((congrArg (push T.toFunctor g) h).trans (push_ret T _ _))

end ContextualComposition.OccurrenceFubini
