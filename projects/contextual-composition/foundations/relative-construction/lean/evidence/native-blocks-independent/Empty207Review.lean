import ContextualComposition.NativeBlocks
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks SpanApex
namespace Empty207
universe b w
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,b,w} B} (S : P.Split)
theorem rest1 : (blocks S 0 1).rest = 𝟭 _ :=
  last_ext (power S 0).dest (Cut.nextRest_pre S (blocks S 0 0)) (Cut.nextRest_grade S (blocks S 0 0))
theorem rest2 : (blocks S 0 2).rest = 𝟭 _ :=
  last_ext (power S 1).dest ((Cut.nextRest_pre S (blocks S 0 1)).trans (congrArg (Cut.pre S (power S 1) ⋙ ·) (rest1 S)))
    (Cut.nextRest_grade S (blocks S 0 1))
example : (blocks S 0 2).joinFunctor = Strict.snd (power S 0).dest (power S 2).source := by
  have h := (blocks S 0 2).join_rest
  rw [rest2 S] at h; exact h
example (n : Nat) : (blocks S n 0).joinFunctor = Strict.fst (power S n).dest (power S 0).source :=
  (blocks S n 0).join_first
end Empty207
