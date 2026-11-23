module
public import ContextualComposition.NativeDependentAssociator
@[expose] public section

/-! The independent associator on three separately collected axes.
The proof uses the three local binary/nullary distributor squares,
never a postulate about a whole triple rectangle. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable (R : Gather S T Z) (L : LeftGather S T Z) (P : TensorPrimitive T)
variable {X Y W : Type w} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
local notation "a" => fold S Z A xs
local notation "b" => fold S Z B ys
local notation "d" => fold S Z D ws
local notation "left" => Lin.left L
local notation "right" => Lin.right R

def tripleIndependentRawLeft :=
  K.seq (act S Z (fun x => act S Z (fun y => (left (T.obj (A x) (B y))).collect D ws) ys) xs)
    (K.seq (act S Z (fun x => ((left (A x)).comp (right d)).collect B ys) xs)
      (((right b).comp (right d)).collect A xs))

def tripleIndependentRawRight :=
  K.seq (act S Z (fun x => act S Z (fun y => ((left (B y)).comp (left (A x))).collect D ws) ys) xs)
    (K.seq (act S Z (fun x => ((right d).comp (left (A x))).collect B ys) xs)
      ((right (T.obj b d)).collect A xs))

variable (Q : PrimitiveLinearity R L P)
include Q in
theorem tripleIndependentRaw_assoc :
    K.seq (tripleIndependentRawLeft R L A B D xs ys ws) (P.assoc a b d) =
      K.seq (act S Z (fun x => act S Z (fun y =>
        act S Z (fun w => P.assoc (A x) (B y) (D w)) ws) ys) xs)
        (tripleIndependentRawRight R L A B D xs ys ws) := by
  have moveX := (Q.ar b d).collect A xs
  have moveY (x : X) := (Q.am (A x) d).collect B ys
  have moveW (x : X) (y : Y) := (Q.al (A x) (B y)).collect D ws
  unfold tripleIndependentRawLeft tripleIndependentRawRight
  simp only [K.assoc, moveX]
  rw [← K.assoc (act S Z (fun x => ((left (A x)).comp (right d)).collect B ys) xs), act_seq]
  simp only [moveY]
  rw [← act_seq]
  simp only [K.assoc]
  rw [← K.assoc (act S Z (fun x => act S Z (fun y => (left (T.obj (A x) (B y))).collect D ws) ys) xs), act_seq]
  have hw (x : X) :
      K.seq (act S Z (fun y => (left (T.obj (A x) (B y))).collect D ws) ys)
        (act S Z (fun y => P.assoc (A x) (B y) d) ys) =
      K.seq (act S Z (fun y => act S Z (fun w => P.assoc (A x) (B y) (D w)) ws) ys)
        (act S Z (fun y => ((left (B y)).comp (left (A x))).collect D ws) ys) := by
    rw [act_seq, act_seq]
    exact congrArg (fun p => act S Z p ys) (funext (moveW x))
  rw [show (fun x => K.seq (act S Z (fun y => (left (T.obj (A x) (B y))).collect D ws) ys)
        (act S Z (fun y => P.assoc (A x) (B y) d) ys)) =
      (fun x => K.seq (act S Z (fun y => act S Z (fun w => P.assoc (A x) (B y) (D w)) ws) ys)
        (act S Z (fun y => ((left (B y)).comp (left (A x))).collect D ws) ys)) from funext hw,
      ← act_seq]
  exact K.assoc _ _ _

end ContextualComposition.NativeFinitePush.DependentFibre
