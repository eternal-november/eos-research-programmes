module

public import WitnessedDecompositions.Core

/-! The default nonempty-signature fragment is closed inside the nullary-enabled syntax. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace WitnessedDecompositions
namespace Path

variable {V : Type u} [Quiver.{v} V]

/-- Expansion of a nonempty profile by nonempty profiles is nonempty. -/
theorem expand_length_pos {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (hp : 0 < p.length) (hf : ∀ i, 0 < (f i).length) : 0 < (expand p f).length := by
  cases p with
  | nil => exact False.elim (Nat.lt_irrefl 0 hp)
  | cons p e =>
      change 0 < ((expand p (fun i => f (.inl i))).comp (f (.inr ()))).length
      rw [Quiver.Path.length_comp]
      exact Nat.lt_of_lt_of_le (hf (.inr ())) (Nat.le_add_left _ _)

end Path
namespace Signature

/-- The positive fragment has no nullary primitive witnesses. -/
def Positive {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V) : Prop :=
  ∀ g, 0 < (S.input g).length

end Signature
namespace Tree

variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Arbitrary positive signatures generate only nonempty operations. -/
theorem frontier_length_pos (hS : S.Positive) {c : Component V} (t : Tree S c) :
    0 < (frontier t).length := by
  induction t with
  | leaf c => exact Nat.zero_lt_one
  | node g children ih => exact Path.expand_length_pos _ _ (hS g) ih

/-- Grafting remains inside the nonempty fragment, with no tree-size bound. -/
theorem graft_frontier_length_pos (hS : S.Positive) {c : Component V}
    (t : Tree S c) (s : Substitution t) : 0 < (frontier (graft t s)).length :=
  frontier_length_pos hS _

end Tree
end WitnessedDecompositions
