/-
Ordered-group refund obstruction, using only Lean 4.35.0 Std and the existing
resource-observation equivalence. No mathlib, new axioms, or proof placeholders.
The constructive main theorem avoids an excluded-middle disjunction.
-/
import ResourceObservationIff
set_option autoImplicit false
universe u
namespace ResourceObservation

/-- Explicit conventional ordered abelian-group axioms, not an observation
property. Monotonicity under right translation implies order reflection because
inverses are present. Antisymmetry is an essential, separate field. -/
structure OrderedAbelianGroupData (G : Type u) where
  add : G → G → G
  zero : G
  neg : G → G
  le : G → G → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  assoc : ∀ a b c, add (add a b) c = add a (add b c)
  comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  translate : ∀ {a b}, le a b → ∀ c, le (add a c) (add b c)

namespace OrderedAbelianGroupData
variable {G : Type u} (g : OrderedAbelianGroupData G)

theorem zero_add (a : G) : g.add g.zero a = a := by
  rw [g.comm, g.add_zero]

theorem mono {a a' c c' : G} (ha : g.le a a') (hc : g.le c c') :
    g.le (g.add a c) (g.add a' c') := by
  have h₁ := g.translate ha c
  have h₂ := g.translate hc a'
  rw [g.comm c a', g.comm c' a'] at h₂
  exact g.trans h₁ h₂

theorem cancel_right {a b c : G} (h : g.le (g.add a c) (g.add b c)) :
    g.le a b := by
  have h' := g.translate h (g.neg c)
  rw [g.assoc, g.assoc, g.add_neg, g.add_zero, g.add_zero] at h'
  exact h'

theorem split (a b : G) : g.add a (g.add (g.neg a) b) = b := by
  rw [← g.assoc, g.add_neg, g.zero_add]

/-- Exact factor domination in a partially ordered group leaves no unobserved
point once even one output point is observed. -/
theorem factor_domination_forces_all (B : Profile G)
    (factor : ObservedFactorDomination g.add g.le B)
    (b : G) (hb : B b) (x : G) : B x := by
  let y := g.add (g.neg x) b
  have hxy : g.add x y = b := g.split x b
  have feasible : g.le (g.add x y) b := by rw [hxy]; exact g.refl b
  rcases factor b hb x y feasible with ⟨a, c, ha, _, hxa, hyc, hac⟩
  have hay : g.le (g.add a y) (g.add x y) := by
    rw [hxy]
    exact g.trans (g.refl _) hac
  have hax := g.cancel_right hay
  have haxEq : a = x := g.antisymm hax hxa
  exact haxEq ▸ ha

/-- Constructive version of “empty or all”: every inhabited observation region
is all of G. This biconditional has only algebraic inputs, not a congruence
assumption disguised among its parameters. -/
theorem universal_agreement_iff_nonempty_forces_all (B : Profile G) :
    UniversalProductAgreement g.add g.le B ↔
      (∀ b, B b → ∀ x, B x) := by
  constructor
  · intro agreement b hb x
    have factor := factor_domination_of_universal_agreement
      g.add g.le g.refl (fun {_ _ _} => g.trans) (fun {_ _ _ _} => g.mono) B agreement
    exact g.factor_domination_forces_all B factor b hb x
  · intro all
    apply (universal_product_agreement_iff_factor
      g.add g.le g.refl (fun {_ _ _} => g.trans) (fun {_ _ _ _} => g.mono) B).mpr
    intro b hb x y hxy
    exact ⟨x, y, all b hb x, all b hb y, g.refl x, g.refl y, hxy⟩

/-- Literal empty/full disjunction with decidability made explicit. -/
theorem universal_agreement_iff_empty_or_all_decidable
    (B : Profile G) [Decidable (∃ b, B b)] :
    UniversalProductAgreement g.add g.le B ↔
      (∀ b, ¬ B b) ∨ (∀ b, B b) := by
  apply Iff.trans (g.universal_agreement_iff_nonempty_forces_all B)
  constructor
  · intro h
    by_cases existsB : ∃ b, B b
    · rcases existsB with ⟨b, hb⟩
      exact Or.inr (h b hb)
    · exact Or.inl (fun b hb => existsB ⟨b, hb⟩)
  · intro h b hb x
    rcases h with empty | all
    · exact False.elim (empty b hb)
    · exact all x

/-- Concrete strict observation regions fail, without any classical principle. -/
theorem nonempty_proper_not_universal (B : Profile G)
    (b x : G) (hb : B b) (hx : ¬ B x) :
    ¬ UniversalProductAgreement g.add g.le B := by
  intro agreement
  exact hx ((g.universal_agreement_iff_nonempty_forces_all B).mp agreement b hb x)
end OrderedAbelianGroupData

/-- Conventional integers instantiate the entire algebraic interface. -/
def integerOrderedGroup : OrderedAbelianGroupData Int where
  add := Int.add
  zero := 0
  neg := Int.neg
  le := (· ≤ ·)
  refl := Int.le_refl
  trans := Int.le_trans
  antisymm := Int.le_antisymm
  assoc := Int.add_assoc
  comm := Int.add_comm
  add_zero := Int.add_zero
  add_neg := Int.add_right_neg
  translate := Int.add_le_add_right

theorem integer_universal_agreement_iff (B : Profile Int) :
    UniversalProductAgreement Int.add (· ≤ ·) B ↔
      (∀ b, B b → ∀ x, B x) :=
  integerOrderedGroup.universal_agreement_iff_nonempty_forces_all B

/-- All nonpositive budgets form a downward-closed region, but refunds defeat
composition: ↑2 and ↑3 look identical there; adding ↑(-2) separates them at 0. -/
theorem integer_refund_counterexample :
    Upward (fun a b : Int => a ≤ b) (fun b => 2 ≤ b) ∧
    Upward (fun a b : Int => a ≤ b) (fun b => 3 ≤ b) ∧
    Upward (fun a b : Int => a ≤ b) (fun b => -2 ≤ b) ∧
    AgreeOn (fun b : Int => b ≤ 0) (fun b => 2 ≤ b) (fun b => 3 ≤ b) ∧
    Product Int.add (· ≤ ·) (fun b => 2 ≤ b) (fun b => -2 ≤ b) 0 ∧
    ¬ Product Int.add (· ≤ ·) (fun b => 3 ≤ b) (fun b => -2 ≤ b) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hab; exact Int.le_trans ha hab
  · intro a b ha hab; exact Int.le_trans ha hab
  · intro a b ha hab; exact Int.le_trans ha hab
  · intro b hb
    constructor
    · intro h
      exact False.elim ((by decide : ¬ ((2 : Int) ≤ 0)) (Int.le_trans h hb))
    · intro h
      exact False.elim ((by decide : ¬ ((3 : Int) ≤ 0)) (Int.le_trans h hb))
  · exact ⟨2, -2, Int.le_refl _, Int.le_refl _, by decide⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    have impossible : (1 : Int) ≤ 0 := Int.le_trans (Int.add_le_add hx hy) hxy
    exact (by decide : ¬ ((1 : Int) ≤ 0)) impossible

theorem integer_nonpositive_is_downward_closed :
    ∀ a b : Int, a ≤ b → b ≤ 0 → a ≤ 0 :=
  fun _ _ hab hb => Int.le_trans hab hb

theorem integer_nonpositive_not_universal :
    ¬ UniversalProductAgreement Int.add (· ≤ ·) (fun b => b ≤ 0) :=
  integerOrderedGroup.nonempty_proper_not_universal (fun b => b ≤ 0)
    0 1 (by decide) (by decide)

#print axioms OrderedAbelianGroupData.mono
#print axioms OrderedAbelianGroupData.cancel_right
#print axioms OrderedAbelianGroupData.factor_domination_forces_all
#print axioms OrderedAbelianGroupData.universal_agreement_iff_nonempty_forces_all
#print axioms OrderedAbelianGroupData.universal_agreement_iff_empty_or_all_decidable
#print axioms OrderedAbelianGroupData.nonempty_proper_not_universal
#print axioms integerOrderedGroup
#print axioms integer_universal_agreement_iff
#print axioms integer_refund_counterexample
#print axioms integer_nonpositive_is_downward_closed
#print axioms integer_nonpositive_not_universal
end ResourceObservation
