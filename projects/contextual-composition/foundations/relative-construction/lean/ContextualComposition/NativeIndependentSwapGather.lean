module
public import ContextualComposition.NativeFubiniDependentAssoc
@[expose] public section

/-! Swapping the two whole independently collected axes. Additive
transposition and multiplicative braiding are different steps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable (R : Gather S T Z) (L : LeftGather S T Z) (P : TensorPrimitive T)
variable {X Y : Type w} (A : X → C) (B : Y → C) (xs : List X) (ys : List Y)
variable (Q : PrimitiveLinearity R L P)
local notation "a" => fold S Z A xs
local notation "b" => fold S Z B ys

include Q in
theorem colGather_swap :
    K.seq (colGather R L A B xs ys) (P.swap a b) =
      K.seq (act S Z (fun y => act S Z (fun x => P.swap (A x) (B y)) xs) ys)
        (rowGather R L B A ys xs) := by
  have h := (Q.sl a).collect B ys
  have k (y : Y) := (Q.sr (B y)).collect A xs
  unfold colGather rowGather tally
  simp only [K.assoc, h, ← collect_right_eq]
  rw [← K.assoc (act S Z (fun y => (Lin.right R (B y)).collect A xs) ys), act_seq]
  simp only [k, ← act_seq, K.assoc]

variable {M : AddCross S Z} (N : GridBinary M R L)
variable {a' b' : C} (p : K.Hom (fold S Z A xs) a') (q : K.Hom (fold S Z B ys) b')

include Q N in
theorem independentCell_swap_transposed :
    K.seq (independentCell R L A B xs ys p q) (P.swap a' b') =
      K.seq (transposeBlock M (fun x y => T.obj (A x) (B y)) ys xs)
        (K.seq (act S Z (fun y => act S Z (fun x => P.swap (A x) (B y)) xs) ys)
          (independentCell R L B A ys xs q p)) := by
  let f := rowGather R L A B xs ys
  let g := colGather R L A B xs ys
  let h := rowGather R L B A ys xs
  let t := transposeBlock M (fun x y => T.obj (A x) (B y)) ys xs
  let b₀ := P.swap a b
  let b₁ := P.swap a' b'
  let s := act S Z (fun y => act S Z (fun x => P.swap (A x) (B y)) xs) ys
  let l := T.map p q
  let r := T.map q p
  have m₀ : K.seq l b₁ = K.seq b₀ r := P.swap_nat p q
  have m₁ : K.seq t g = f := row_col_gather M R L N A B xs ys
  have m₂ : K.seq g b₀ = K.seq s h := colGather_swap R L P A B xs ys Q
  change K.seq (K.seq f l) b₁ = K.seq t (K.seq s (K.seq h r))
  calc
    _ = K.seq f (K.seq l b₁) := K.assoc _ _ _
    _ = K.seq f (K.seq b₀ r) := congrArg (K.seq f) m₀
    _ = K.seq (K.seq t g) (K.seq b₀ r) := congrArg (fun x => K.seq x (K.seq b₀ r)) m₁.symm
    _ = K.seq t (K.seq g (K.seq b₀ r)) := K.assoc _ _ _
    _ = K.seq t (K.seq (K.seq g b₀) r) := congrArg (K.seq t) (K.assoc _ _ _).symm
    _ = K.seq t (K.seq (K.seq s h) r) := congrArg (fun u => K.seq t (K.seq u r)) m₂
    _ = _ := congrArg (K.seq t) (K.assoc _ _ _)

end ContextualComposition.NativeFinitePush.DependentFibre
