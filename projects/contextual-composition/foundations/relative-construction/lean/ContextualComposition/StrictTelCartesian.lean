module
public import ContextualComposition.StrictTelNested
public import ContextualComposition.StrictSpanCart
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelCartesian
open CategoryTheory SpanApex NativeBlocks NativeCleavage
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictSpanCart StrictTelFold StrictTelNested
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option linter.style.haveILetI false
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

def tag (n : Nat) : Over (power S n) (whole S) := ⟨incl S n,rfl,rfl⟩
theorem tagCart (n : Nat) : CartesianMap (tag S n) := by
  intro x y f h
  exact (BlockCartesian.cartesian_iff (incl S n) (BlockCartesian.inclIncoming n) (leftLeg S) f).mp h

theorem joinCart (m n : Nat) : CartesianMap (concatenate S m n) := by
  letI : (concatenate S m n).functor.IsIso := (blocks S m n).strictIso.symm.isIso_functor
  intro x y f h
  exact isomorphism (concatenate S m n) f h

def cutLast (n : Nat) : Over (power S (n+1)) (Pair (power S n) (power S 1)) where
  functor := Strict.lift _ _ (NativeAssoc.front S n) (NativeAssoc.last S n) (NativeAssoc.boundary S n)
  source := NativeAssoc.last_src S n
  dest := NativeAssoc.last_dst S n

instance cutIso (n : Nat) : (cutLast S n).functor.IsIso := by
  cases n <;> exact NativeBlocks.lastIso _

theorem snocFactor (n : Nat) (M : Ops (power S 1)) (E : Over (power S n) (power S 1)) :
    snoc S M E = StrictSpanAlgebra.comp
      (StrictSpanAlgebra.comp (cutLast S n) (both E (StrictSpanAlgebra.id _))) M.tensor := by
  apply overExt
  exact (congrArg (· ⋙ M.tensor.functor) (combine_both E (StrictSpanAlgebra.id _) (NativeAssoc.front S n)
    (NativeAssoc.last S n) (NativeAssoc.boundary S n))).symm

variable (M : Ops (power S 1))

theorem combCart (a : CartesianMap M.unit) (m : CartesianMap M.tensor)
    (n : Nat) : CartesianMap (comb S M n) := by
  induction n with
  | zero => exact a
  | succ k ih =>
    cases k with
    | zero => exact identity _
    | succ k =>
      change CartesianMap (snoc S M (comb S M (k+1)))
      rw [snocFactor]
      exact compose (compose (isomorphism (cutLast S (k+1))) (bothCart (SpanPull.All.parts S (k+1))
        (SpanPull.All.parts S 1) ih (identity _))) m

theorem evalCart (a : CartesianMap M.unit) (m : CartesianMap M.tensor) :
    CartesianMap (eval S M) := by
  intro x y f h
  obtain ⟨n,x⟩ := x; obtain ⟨j,y⟩ := y
  cases f with
  | mk f =>
    have k := (BlockCartesian.cartesian_iff (incl S n) (BlockCartesian.inclIncoming n) (leftLeg S) f).mpr h
    exact combCart S M a m n f k

theorem restrictedUnitCart {A : Over (whole S) (power S 1)} (h : CartesianMap A) :
    CartesianMap (readOperations S A).unit :=
  compose (tagCart S 0) h

theorem restrictedTensorCart {A : Over (whole S) (power S 1)} (h : CartesianMap A) :
    CartesianMap (readOperations S A).tensor :=
  compose (joinCart S 1 1) (compose (tagCart S 2) h)

end ContextualComposition.GrothendieckStep.StrictTelCartesian
