module
public import ContextualComposition.NativeFubiniThirdData
@[expose] public section

/-! Whisker the actual binary Fubini comparison into the parent or
continuation slot. The order-aware scalar preservation comes from
the checked binary Fubini augmentation, including at unused rows. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C} {A B : OrderedDependentAugData I}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (D : OrderedDependentThirdData A) (E : OrderedDependentThirdData B)
local notation "prd" => ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData.product R L J
local notation "leftD" => leftData R L J D
local notation "leftE" => leftData R L J E
local notation "rightD" => rightData R L J D
local notation "rightE" => rightData R L J E
local notation "joint" => product R L J D E

set_option backward.isDefEq.respectTransparency false in
noncomputable def parentFubiniComparison :
    OrderedDependentAugData.ReadComparison (prd leftD leftE) (leftData R L J joint) where
  parent := binaryFubini_scalarComparison R L J N NR NL m mi h j unit_middle hl hr
    A.xs B.xs A.us B.us A.V B.V A.A B.A A.δ B.δ A.ε B.ε
  child t := WordAugReadComparison.scalarIdent ((prd leftD leftE).A t) ((prd leftD leftE).us t) ((prd leftD leftE).δ t)

set_option backward.isDefEq.respectTransparency false in
noncomputable def tailFubiniComparison :
    OrderedDependentAugData.ReadComparison (prd rightD rightE) (rightData R L J joint) where
  parent := WordAugReadComparison.scalarIdent (prd A B).V (prd A B).xs (prd A B).ε
  child t := binaryFubini_scalarComparison R L J N NR NL m mi h j unit_middle hl hr
    (A.us t.1) (B.us t.2) (D.ws t.1) (E.ws t.2) (A.A t.1) (B.A t.2) (D.D t.1) (E.D t.2)
    (D.γ t.1) (E.γ t.2) (A.δ t.1) (B.δ t.2)

noncomputable def whiskerParentFubini :=
  (parentFubiniComparison R L J N NR NL m mi h j unit_middle hl hr D E).accumulate R L J NL hl

noncomputable def whiskerTailFubini :=
  (tailFubiniComparison R L J N NR NL m mi h j unit_middle hl hr D E).accumulate R L J NL hl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
