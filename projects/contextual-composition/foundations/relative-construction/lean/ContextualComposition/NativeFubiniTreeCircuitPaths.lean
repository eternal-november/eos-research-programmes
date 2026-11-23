module
public import ContextualComposition.NativeFubiniTreeCircuitRoots
@[expose] public section

/-! Actual source and scalar circuit interpretations of any tagged path. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [cat : Category.{v} C] [add : MonoidalCategory C] [sa : SymmetricCategory C]
variable (M : TensorSemantics C) {Tag : Type w}
set_option quotPrecheck false in
local notation "𝕄" => (M).tensor
set_option quotPrecheck false in
local notation "𝕊" => (M).symmetric
set_option quotPrecheck false in
local notation "Iₘ" => @MonoidalCategoryStruct.tensorUnit C cat (𝕄).toMonoidalCategoryStruct
set_option quotPrecheck false in
local notation "Tree" => @DependentFubiniTree C cat add sa (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct)
local notation "Π" => binary (@Binary.ofMonoidal C cat 𝕄)
set_option quotPrecheck false in
local notation "P" => @tensorPrimitives C cat 𝕄 (𝕊).toBraidedCategory
local notation "ℙ" => @standardPush C cat add sa
set_option quotPrecheck false in
local notation "αₘ" => @MonoidalCategoryStruct.associator C cat (𝕄).toMonoidalCategoryStruct
set_option quotPrecheck false in
local notation "βₘ" => @BraidedCategory.braiding C cat 𝕄 (𝕊).toBraidedCategory
set_option quotPrecheck false in
local notation "ρₘ" => @MonoidalCategoryStruct.rightUnitor C cat (𝕄).toMonoidalCategoryStruct

variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) (binary (@Binary.ofMonoidal C cat M.tensor)) (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) (binary (@Binary.ofMonoidal C cat M.tensor)) (𝟙_ C))
variable (J : UnitCompat R (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (Q : PrimitiveLinearity R L (@tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory))
variable (U : AssocRightUnit R J (@tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory))
variable [lF : ∀ a : C, (leftFactor (binary (@Binary.ofMonoidal C cat M.tensor)) a).LaxBraided]
variable [rF : ∀ b : C, (rightFactor (T:=binary (@Binary.ofMonoidal C cat M.tensor)) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather (binary (@Binary.ofMonoidal C cat M.tensor)) a L) (hr : ∀ b : C, SameRightGather R b)
variable (ia : ∀ a b c, IsIso ((@tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory).assoc a b c))
variable (is : ∀ a b, IsIso ((@tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory).swap a b))
variable (iu : ∀ a, IsIso (J.ρ a))
variable (su : (@tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory).swap _ _ ≫ J.ρ _ = J.ρ _)
variable (unit_eq : ∀ c, J.ρ c = (@MonoidalCategoryStruct.rightUnitor C cat M.tensor.toMonoidalCategoryStruct c).hom)

local notation "fr" => separateTagFrame R L J
local notation "lc" => separateCoeff (T:=Π)
local notation "ra" => separateAssoc P R L J NR NL Q U hl hr ia

local notation "asIso₀" => AssocMove.separateIso R L J N NR NL hl hr P Q U ia
local notation "stIso₀" => StructuralMove.separateIso R L J N NR NL hl hr P Q U ia su is iu
local notation "pathIso₀" => StructuralPath.separateIso R L J N NR NL hl hr P Q U ia su is iu

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
noncomputable def AssocMove.circuitTraceForward {a b : Tree} (p : AssocMove a b) (s : Tagging Tag a) :
    CircuitTrace M R L J (p.tagForward s) (asIso₀ p).hom.native := by
  induction p with
  | root a b c =>
    cases s with | fork ab c₀ =>
      cases ab with | fork a₀ b₀ =>
        exact assocRootCircuitTrace M R L J NR NL Q U hl hr ia a b c a₀ b₀ c₀
  | left f c ih =>
    cases s with | fork a c =>
      exact CircuitTrace.tensor M R L J hl hr (ih a) (CircuitTrace.ident M R L J c)
  | right c f ih =>
    cases s with | fork c a =>
      exact CircuitTrace.tensor M R L J hl hr (CircuitTrace.ident M R L J c) (ih a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
noncomputable def AssocMove.circuitTraceBackward {a b : Tree} (p : AssocMove a b) (s : Tagging Tag b) :
    CircuitTrace M R L J (p.tagBackward s) (asIso₀ p).inv.native := by
  induction p with
  | root a b c =>
    cases s with | fork a₀ bc =>
      cases bc with | fork b₀ c₀ =>
        let f := AssocMove.root a b c
        let C := assocRootCircuitTrace M R L J NR NL Q U hl hr ia a b c a₀ b₀ c₀
        exact CircuitTrace.reverse M R L J (asIso₀ f) C (fun V z h => f.tagBackward_matches V _ z h)
  | left f c ih =>
    cases s with | fork a c =>
      exact CircuitTrace.tensor M R L J hl hr (ih a) (CircuitTrace.ident M R L J c)
  | right c f ih =>
    cases s with | fork c a =>
      exact CircuitTrace.tensor M R L J hl hr (CircuitTrace.ident M R L J c) (ih a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5500000 in
include unit_eq in
noncomputable def StructuralMove.circuitTraceForward {a b : Tree} (p : StructuralMove a b) (s : Tagging Tag a) :
    CircuitTrace M R L J (p.tagForward s) (stIso₀ p).hom.native := by
  induction p with
  | assoc p => exact p.circuitTraceForward M R L J N NR NL Q U hl hr ia s
  | swap a b =>
    cases s with | fork u v =>
      exact swapRootCircuitTrace M R L J N Q is su a b u v
  | eraseRight a =>
    cases s with | fork u v =>
      cases v
      exact runitRootCircuitTrace M R L J hl iu unit_eq a u
  | left f c ih =>
    cases s with | fork a c =>
      exact CircuitTrace.tensor M R L J hl hr (ih a) (CircuitTrace.ident M R L J c)
  | right c f ih =>
    cases s with | fork c a =>
      exact CircuitTrace.tensor M R L J hl hr (CircuitTrace.ident M R L J c) (ih a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5500000 in
include unit_eq in
noncomputable def StructuralMove.circuitTraceBackward {a b : Tree} (p : StructuralMove a b) (s : Tagging Tag b) :
    CircuitTrace M R L J (p.tagBackward s) (stIso₀ p).inv.native := by
  induction p with
  | assoc p => exact p.circuitTraceBackward M R L J N NR NL Q U hl hr ia s
  | swap a b =>
    cases s with | fork v u =>
      let f := StructuralMove.swap a b
      let C := swapRootCircuitTrace M R L J N Q is su a b u v
      exact CircuitTrace.reverse M R L J (stIso₀ f) C (fun V z h => f.tagBackward_matches V _ z h)
  | eraseRight a =>
    let f := StructuralMove.eraseRight a
    let C := runitRootCircuitTrace M R L J hl iu unit_eq a s
    exact CircuitTrace.reverse M R L J (stIso₀ f) C (fun V z h => f.tagBackward_matches V _ z h)
  | left f c ih =>
    cases s with | fork a c =>
      exact CircuitTrace.tensor M R L J hl hr (ih a) (CircuitTrace.ident M R L J c)
  | right c f ih =>
    cases s with | fork c a =>
      exact CircuitTrace.tensor M R L J hl hr (CircuitTrace.ident M R L J c) (ih a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
include unit_eq in
noncomputable def StructuralPath.circuitTrace {a b : Tree} (p : StructuralPath a b) (s : Tagging Tag a) :
    CircuitTrace M R L J (p.tagTransport s) (pathIso₀ p).hom.native := by
  induction p with
  | ident a => exact CircuitTrace.ident M R L J s
  | next f g ih =>
    exact CircuitTrace.comp M R L J (f.circuitTraceForward M R L J N NR NL Q U hl hr ia is iu su unit_eq s)
      (ih (f.tagForward s).target)
  | prev f g ih =>
    exact CircuitTrace.comp M R L J (f.circuitTraceBackward M R L J N NR NL Q U hl hr ia is iu su unit_eq s)
      (ih (f.tagBackward s).target)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
