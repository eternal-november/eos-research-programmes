module
public import ContextualComposition.OccurrenceFubini
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Function.Basic

/-! Independence of the finite position chart for commutative sequencing. Optional cells are used only in the proof to compare different orders of writes. The resulting effect is on a total dependent tuple. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.OccurrenceFubiniPermutation
open CategoryTheory CouplingPullbacks DependentConeInterchange OccurrenceFubini
universe u
variable (T : CategoryTheory.Monad (Type u))

/-- The two independent draws commute before every common continuation. -/
def Exchange := ∀ {X Y Z : Type u} (p : T.obj X) (q : T.obj Y) (k : X → Y → T.obj Z),
  bind T p (fun x => bind T q (k x)) = bind T q (fun y => bind T p (fun x => k x y))

/-- Equality of the two ordinary binary Fubini maps into the ordered pair type. -/
def Commutative := ∀ {X Y : Type u} (p : T.obj X) (q : T.obj Y),
  bind T p (fun x => push T.toFunctor (Prod.mk x) q) =
    bind T q (fun y => push T.toFunctor (fun x => (x,y)) p)

theorem exchange_iff : Exchange T ↔ Commutative T := by
  have pureBind {X Y : Type u} (p : T.obj X) (f : X → Y) :
      bind T p (fun x => ret T (f x)) = push T.toFunctor f p :=
    (bind_push T p f (ret T)).symm.trans (bind_ret T _)
  constructor
  · intro h X Y p q
    simpa only [pureBind] using h p q (fun x y => ret T (x,y))
  · intro h X Y Z p q k
    have eq := congrArg (fun z => bind T z (fun xy : X × Y => k xy.1 xy.2)) (h p q)
    simpa only [bind_assoc,bind_push,Function.comp_def] using eq

variable {I : Type u} {A : I → Type u} {Z : Type u}
abbrev Env (A : I → Type u) := ∀ i, Option (A i)
def put (e : Env A) (i : I) (x : A i) : Env A := by
  classical
  exact Function.update e i (some x)

def run (p : ∀ i, T.obj (A i)) : List I → Env A → (Env A → T.obj Z) → T.obj Z
  | [], e, k => k e
  | i :: is, e, k => bind T (p i) (fun x => run p is (put e i x) k)

theorem run_perm (comm : Exchange T) (p : ∀ i, T.obj (A i)) {is js : List I} (h : is.Perm js)
    (e : Env A) (k : Env A → T.obj Z) : run T p is e k = run T p js e k := by
  classical
  induction h generalizing e with
  | nil => rfl
  | cons i h ih => exact congrArg (bind T (p i)) (funext fun x => ih (put e i x))
  | swap i j tail =>
    by_cases eq : j = i
    · subst j; rfl
    · simp only [run]
      rw [comm (p j) (p i)]
      apply congrArg (bind T (p i)); funext x
      apply congrArg (bind T (p j)); funext y
      exact congrArg (fun env => run T p tail env k) (Function.update_comm eq _ _ _)
  | trans _ _ h₁ h₂ => exact (h₁ e).trans (h₂ e)

def store : (n : Nat) → (f : Fin n → I) → (∀ j, A (f j)) → Env A → Env A
  | 0, _, _, e => e
  | n+1, f, x, e => store n (fun j => f j.succ) (fun j => x j.succ) (put e (f 0) (x 0))

theorem run_ofFn (p : ∀ i, T.obj (A i)) (n : Nat) (f : Fin n → I) (e : Env A) (k : Env A → T.obj Z) :
    run T p (List.ofFn f) e k =
      bind T (productFin T n (fun j => p (f j))) (fun xs => k (store n f xs e)) := by
  induction n generalizing e with
  | zero => simp only [List.ofFn_zero,run,productFin,ret_bind,store]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [run, productFin, bind_assoc]
    apply congrArg (bind T (p (f 0))); funext x
    rw [ih, bind_push]
    rfl

private def storeAll (w : ∀ i, A i) : List I → Env A → Env A
  | [], e => e
  | i :: is, e => storeAll w is (put e i (w i))

private theorem store_values (w : ∀ i, A i) (n : Nat) (f : Fin n → I) (e : Env A) :
    store n f (fun i => w (f i)) e = storeAll w (List.ofFn f) e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => rw [List.ofFn_succ]; exact ih _ _

private theorem stays (w : ∀ i, A i) (is : List I) (e : Env A) (i : I)
    (h : i ∈ is ∨ e i = some (w i)) : storeAll w is e i = some (w i) := by
  classical
  induction is generalizing e with
  | nil => simpa [storeAll] using h
  | cons j js ih =>
    apply ih
    by_cases eq : i = j
    · subst j; exact Or.inr (by simp [put])
    · simpa [put,Function.update_of_ne eq,eq] using h

def productBy {n : Nat} (chart : I ≃ Fin n) (p : ∀ i, T.obj (A i)) : T.obj (∀ i, A i) :=
  push T.toFunctor (Equiv.piCongrLeft' A chart).symm (productFin T n (fun j => p (chart.symm j)))

private def finish (fallback : T.obj (∀ i, A i)) (e : Env A) : T.obj (∀ i, A i) := by
  classical
  exact if ok : ∀ i, (e i).isSome then ret T (fun i => (e i).get (ok i)) else fallback

private theorem run_chart {n : Nat} (chart : I ≃ Fin n) (p : ∀ i, T.obj (A i)) (fb : T.obj (∀ i, A i)) :
    run T p (List.ofFn chart.symm) (fun _ => none) (finish T fb) = productBy T chart p := by
  classical
  let a := Equiv.piCongrLeft' A chart
  rw [run_ofFn]
  change bind T _ _ = push T.toFunctor a.symm _
  rw [← bind_ret T (push T.toFunctor a.symm _),bind_push]
  apply congrArg (bind T _)
  funext xs
  let w := a.symm xs
  have matchValues : (fun j => w (chart.symm j)) = xs := a.apply_symm_apply xs
  have st : store n (⇑chart.symm) xs (fun _ => none) = fun i => some (w i) := by
    rw [← matchValues,store_values]
    funext i
    exact stays w _ _ _ (Or.inl (List.mem_ofFn.mpr ⟨chart i,chart.symm_apply_apply i⟩))
  change finish T fb (store n (⇑chart.symm) xs (fun _ => none)) = ret T w
  rw [st]
  simp [finish]

theorem independent_of_chart (comm : Exchange T) {n m : Nat} (a : I ≃ Fin n) (b : I ≃ Fin m)
    (p : ∀ i, T.obj (A i)) : productBy T a p = productBy T b p := by
  classical
  have perm : (List.ofFn a.symm).Perm (List.ofFn b.symm) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective a.symm.injective)
      (List.nodup_ofFn_ofInjective b.symm.injective)).mpr
    intro i
    exact ⟨fun _ => List.mem_ofFn.mpr ⟨b i,b.symm_apply_apply i⟩,
      fun _ => List.mem_ofFn.mpr ⟨a i,a.symm_apply_apply i⟩⟩
  let fallback := productBy T a p
  exact (run_chart T a p fallback).symm.trans ((run_perm T comm p perm _ _).trans (run_chart T b p fallback))

theorem frontier_product_eq [Finite I] (comm : Exchange T) {n : Nat} (e : I ≃ Fin n) (p : ∀ i, T.obj (A i)) :
    product T p = productBy T e p := by
  classical
  let := Fintype.ofFinite I
  exact independent_of_chart T comm (Fintype.equivFin I) e p

end ContextualComposition.OccurrenceFubiniPermutation
