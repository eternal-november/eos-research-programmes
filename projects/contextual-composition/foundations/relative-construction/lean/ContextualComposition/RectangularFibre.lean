module

public import ContextualComposition.AddressedFubini

@[expose] public section

/-! Rectangular occurrence domains; the construction is a row-major nested
sum, not a coproduct or a tensor of sums by definition. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w t
variable {C : Type u} {K : Coeff.{u,v} C} {T S : Bi K} {Z U : C}
variable (G : Gather S T Z) (L : LeftGather S T Z)
def innerLeft {X : Type w} (a : C) (W : X → C) : (ys : List X) →
    K.Hom (fold S Z (fun y => T.obj a (W y)) ys) (T.obj a (fold S Z W ys))
  | [] => L.nil a
  | y::ys => K.seq (S.map (K.id _) (innerLeft a W ys)) (L.cons a (W y) _)
/-- Single rectangle with row-major multiplicative labels, then arbitrary
whole-axis arrows. -/
def rect {X Y : Type w} (V : X → C) (W : Y → C) (xs : List X) (ys : List Y) :
    K.Hom (fold S Z (fun x => fold S Z (fun y => T.obj (V x) (W y)) ys) xs)
      (T.obj (fold S Z V xs) (fold S Z W ys)) :=
  K.seq (act S Z (fun x => innerLeft L (V x) W ys) xs) (gather G V _ xs)

variable {I : Type w} {X : I → Type t} (ix : ∀ i, List (X i)) (A : ∀ i, X i → C)
/-- A rectangular source at fixed independent target, including empty axes.
For each slot the source is its *list of coefficient leaves*, not their sum.
Tensor bracketing (including the terminal unit) follows the occurrence list. -/
def cube (S T : Bi K) (Z U : C) (is : List I) (F : C → C) : C :=
  match is with
  | [] => F U
  | i::js => fold S Z (fun x => cube S T Z U js (fun y => F (T.obj (A i x) y))) (ix i)
/-- Gather a suffix into an arbitrary tensor context F. The caller supplies
distribution of that context across the sums. Instead of assuming coherence
for composite contexts, build gathering one outer tensor at a time. -/
def underLeft (a : C) (is : List I) (F : C → C) :
    K.Hom (cube ix A S T Z U is (fun x => T.obj a (F x))) (T.obj a (cube ix A S T Z U is F)) :=
  match is with
  | [] => K.id _
  | i::js =>
    K.seq (act S Z (fun x => underLeft a js (fun y => F (T.obj (A i x) y))) (ix i))
      (innerLeft L a _ (ix i))
def cubeGather : (is : List I) →
    K.Hom (cube ix A S T Z U is id) (fold T U (fun i => fold S Z (A i) (ix i)) is)
  | [] => K.id U
  | i::js =>
    K.seq (act S Z (fun x => underLeft L ix A (A i x) js id) (ix i))
      (K.seq (gather G (A i) _ (ix i)) (T.map (K.id _) (cubeGather js)))

def boxMap {B : I → C} (ar : ∀ i, K.Hom (fold S Z (A i) (ix i)) (B i)) (is : List I) :
    K.Hom (cube ix A S T Z U is id) (fold T U B is) :=
  K.seq (cubeGather G L ix A is) (act T U ar is)

theorem boxMap_post {B D : I → C} (ar : ∀ i, K.Hom (fold S Z (A i) (ix i)) (B i))
    (q : ∀ i, K.Hom (B i) (D i)) (is : List I) :
    K.seq (boxMap G L ix A ar is) (act T U q is) =
    boxMap G L ix A (fun i => K.seq (ar i) (q i)) is := by
  unfold boxMap
  rw [K.assoc, act_seq]

variable (M : Middle T U)
/-- Product of the outer address lists, retaining the inner ragged fibre sums
as leaves. The equality compares actual arrows out of this nested-sum object. -/
theorem boxDep (ds : I → Fibre (S:=S) (Z:=Z)) (is : List I) :
    K.seq (boxMap G L (fun i => (ds i).xs)
      (fun i => rowSource (T:=T) (S:=S) (Z:=Z) (ds i).V (ds i).J)
      (fun i => dep G (ds i).V (ds i).J L (ds i).xs (ds i).β (ds i).α) is)
      (shuffle M (fun i => (ds i).a) (fun i => (ds i).b) is) =
    K.seq (cubeGather G L (fun i => (ds i).xs)
      (fun i => rowSource (T:=T) (S:=S) (Z:=Z) (ds i).V (ds i).J) is)
      (K.seq (act T U (fun i => ((ds i).stage G L).before) is)
        (K.seq (shuffle M (fun i => fold S Z (ds i).V (ds i).xs) (fun i => (ds i).b) is)
          (T.map (act T U (fun i => (ds i).α) is) (act T U (fun i => K.id (ds i).b) is)))) := by
  unfold boxMap
  rw [K.assoc, addressedDep]
  rfl
end ContextualComposition.NativeFinitePush.DependentFibre
