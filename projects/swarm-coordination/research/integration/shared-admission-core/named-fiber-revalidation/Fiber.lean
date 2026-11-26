import Mathlib

namespace SwarmFiber

/-- A live fiber blocks an action exactly when its menu excludes it. -/
def blocks {A : Type} (x : Option (A → Bool)) (a : A) : Nat :=
  match x with
  | none => 0
  | some m => if m a then 0 else 1

theorem appendZero {A : Type} (x y : List (Option (A → Bool))) (a : A) :
    (((x ++ y).map fun p => blocks p a).sum = 0) ↔
      ((x.map fun p => blocks p a).sum = 0 ∧
       (y.map fun p => blocks p a).sum = 0) := by
  simp [List.sum_append]

theorem counterReplace (unaffected previous next : Nat) :
    (unaffected + previous) - previous + next = unaffected + next := by omega

/-- Drop all profiles except an optional menu at the named fiber. -/
def isolate {I M : Type} [DecidableEq I] (f : I → Option M) (i j : I) :=
  if i = j then f j else none

theorem isolatedInjective {I M : Type} [DecidableEq I] :
    Function.Injective (fun f : I → Option M => fun i => isolate f i i) := by
  intro x y h
  funext i
  simpa [isolate] using congrFun h i

theorem zeroExactlyAll {A : Type} (ps : List (Option (A → Bool))) (a : A) :
    (ps.map (fun p => blocks p a)).sum = 0 ↔
      ∀ menu : A → Bool, some menu ∈ ps → menu a = true := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    cases p with
    | none => simpa [blocks] using ih
    | some m =>
      cases hm : m a <;> simp_all [blocks]

theorem countExact (n m : Nat) :
    Fintype.card (Fin n → Option (Fin m → Bool)) = (2 ^ m + 1) ^ n := by
  simp

end SwarmFiber

#print axioms SwarmFiber.appendZero
#print axioms SwarmFiber.counterReplace
#print axioms SwarmFiber.isolatedInjective
#print axioms SwarmFiber.countExact
#print axioms SwarmFiber.zeroExactlyAll
