module
public import ContextualComposition.NativeDependentPairFunctoriality
@[expose] public section

/-! Natural Fubini for arbitrary families in the native finite category.
The source inputs and arrows no longer require caller-provided words. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

namespace NativeDependentPair

set_option backward.isDefEq.respectTransparency false in
theorem product_parent_aug (A B : NativeDependentPair I) :
    let P := A.ordered.product R L J B.ordered
    wordAug P.V P.xs P.ε = independentAug R L (J.ρ I) A.parent B.parent := by
  intro P
  have h := independentAug_ordered_eq R L (J.ρ I) A.ordered.V B.ordered.V A.ordered.xs B.ordered.xs
    A.ordered.ε B.ordered.ε
  change _ = wordAug P.V P.xs P.ε at h
  rw [← h, A.parent_recovers, B.parent_recovers]

set_option backward.isDefEq.respectTransparency false in
theorem product_child_aug (A B : NativeDependentPair I) (x : Fin A.parent.base.n) (y : Fin B.parent.base.n) :
    let P := A.ordered.product R L J B.ordered
    let z : P.X := (⟨x⟩,⟨y⟩)
    wordAug (P.A z) (P.us z) (P.δ z) = independentAug R L (J.ρ I) (A.child x) (B.child y) := by
  intro P z
  have h := independentAug_ordered_eq R L (J.ρ I)
    (A.ordered.A ⟨x⟩) (B.ordered.A ⟨y⟩) (A.ordered.us ⟨x⟩) (B.ordered.us ⟨y⟩)
    (A.ordered.δ ⟨x⟩) (B.ordered.δ ⟨y⟩)
  change _ = wordAug (P.A z) (P.us z) (P.δ z) at h
  rw [← h, A.child_recovers, B.child_recovers]

end NativeDependentPair

variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

noncomputable def finiteFamilyFubini (n : Nat) (A : Fin n → NativeDependentPair I) :
    NativeAugmentedIso (independentAugFold R L (J.ρ I) n (fun i => (A i).accumulate R L J))
      ((dependentInputFold R L J n (fun i => (A i).ordered)).accumulate R L J) :=
  orderedFubini R L N NR NL hl hr J m mi h j unit_middle n (fun i => (A i).ordered)

set_option backward.isDefEq.respectTransparency false in
theorem finiteFamilyFubini_natural (n : Nat) {A B : Fin n → NativeDependentPair I}
    (p : ∀ i, NativeDependentPairHom (A i) (B i)) :
    (independentAugFoldMap R L (J.ρ I) N NR NL hl hr n (fun i => (p i).accumulate R L J N NL hl)).comp
      (finiteFamilyFubini R L J N NR NL hl hr m mi h j unit_middle n B).hom =
    (finiteFamilyFubini R L J N NR NL hl hr m mi h j unit_middle n A).hom.comp
      ((dependentInputFoldMap R L N NR NL hl hr J n (fun i => (p i).ordered)).accumulate R L J N NL hl) :=
  orderedFubini_natural R L N NR NL hl hr J m mi h j unit_middle n (fun i => (p i).ordered)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
