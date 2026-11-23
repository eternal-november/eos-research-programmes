module
public import ContextualComposition.NativeAdmissibleFubiniTree
public import ContextualComposition.NativeFubiniTreePathCoherence
@[expose] public section

/-! Tagged path independence for actual admissible indexed Fubini objects. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily.AdmissibleFubiniTree
open DependentFubiniTree
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

variable (m : Middle (binary (@Binary.ofMonoidal C cat M.tensor))
  (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))
variable (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell _ _ _ _ ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))]

variable {A : Type u} {K : NativeProjectionClass.{u}}
set_option quotPrecheck false in
local notation "DTree" => @AdmissibleFubiniTree C cat add sa K A
  (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct)
local notation "ps" => pathSeparateIso R L J N NR NL hl hr P Q U ia su is iu
local notation "pj" => pathJointIso R L J N NR NL hl hr P Q U ia su is iu

set_option backward.isDefEq.respectTransparency false in
omit [IsIso (J.ρ (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))] in
include m mi h j unit_middle unit_eq in
theorem path_coherent_of_tag_word {a b : DTree}
    (p q : ∀ x : A, StructuralPath (a.eval x) (b.eval x))
    (law : FubiniTreeLaws R J P m)
    (tags : ∀ x, ((p x).tagTransport (tagsFrom 0 (a.eval x))).target.expr.leaves =
      ((q x).tagTransport (tagsFrom 0 (a.eval x))).target.expr.leaves) :
    (ps p).hom = (ps q).hom ∧ (pj p).hom = (pj q).hom := by
  have e x := (p x).coherent_of_tag_word M R L J N NR NL Q U hl hr ia is iu su unit_eq
    m mi h j unit_middle (q x) law (tags x)
  constructor
  · apply ObjectProperty.hom_ext
    exact funext fun x => (e x).1
  · apply ObjectProperty.hom_ext
    exact funext fun x => (e x).2

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily.AdmissibleFubiniTree
