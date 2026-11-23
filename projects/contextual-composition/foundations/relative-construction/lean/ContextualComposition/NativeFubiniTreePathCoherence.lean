module
public import ContextualComposition.NativeFubiniTreeTaggedBranches
@[expose] public section

/-! Path independence at the actual augmented native endpoints. -/
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

local notation "pIso" => StructuralPath.separateIso R L J N NR NL hl hr P Q U ia su is iu
local notation "jIso" => StructuralPath.jointIso R L J N NR NL hl hr P Q U ia su is iu

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
include unit_eq in
/-- In the actual separate product, equal addressed permutations
give equal native augmented arrows. The typed carrier equality is
derived from the tagged branches, not supplied. -/
theorem StructuralPath.separate_coherent {a b : Tree} (p q : StructuralPath a b)
    (s : Tagging Tag a) (hn : s.expr.leaves.Nodup)
    (ht : (p.tagTransport s).target = (q.tagTransport s).target) :
    (pIso p).hom = (pIso q).hom := by
  have f := p.circuitTrace M R L J N NR NL Q U hl hr ia is iu su unit_eq s
  have g := q.circuitTrace M R L J N NR NL Q U hl hr ia is iu su unit_eq s
  have hr := p.read_eq_of_tags q s hn ht
  apply AugHom.ext
  exact CircuitTrace.eq M R L J f g hn ht hr (fun z =>
    s.exists_labels (T:=Π) hn z)

variable (m : Middle (binary (@Binary.ofMonoidal C cat M.tensor))
  (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))
variable (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell _ _ _ _ ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))]
local notation "ph" => comparison R L J N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
include unit_eq mi h j unit_middle in
/-- Path independence descends to the independently constructed joint
arrows via the actual Fubini isomorphism. -/
theorem StructuralPath.joint_coherent {a b : Tree} (p q : StructuralPath a b)
    (law : FubiniTreeLaws R J P m) (s : Tagging Tag a) (hn : s.expr.leaves.Nodup)
    (ht : (p.tagTransport s).target = (q.tagTransport s).target) :
    (jIso p).hom = (jIso q).hom := by
  let x := ph a
  let y := ph b
  let f := (jIso p).hom
  let g := (jIso q).hom
  have h₀ : (pIso p).hom = (pIso q).hom :=
    p.separate_coherent M R L J N NR NL Q U hl hr ia is iu su unit_eq q s hn ht
  have h₁ : x.hom.comp f = x.hom.comp g := by
    have p₀ := p.fubini R L J N NR NL hl hr P Q U ia su is iu m mi h j unit_middle law
    have q₀ := q.fubini R L J N NR NL hl hr P Q U ia su is iu m mi h j unit_middle law
    change (pIso p).hom.comp y.hom = x.hom.comp f at p₀
    change (pIso q).hom.comp y.hom = x.hom.comp g at q₀
    exact p₀.symm.trans ((congrArg (fun t => t.comp y.hom) h₀).trans q₀)
  change f = g
  calc
    f = (x.inv.comp x.hom).comp f := by rw [x.inv_hom, AugHom.ident_comp]
    _ = x.inv.comp (x.hom.comp f) := AugHom.comp_assoc _ _ _
    _ = x.inv.comp (x.hom.comp g) := congrArg (fun k => x.inv.comp k) h₁
    _ = g := by rw [← AugHom.comp_assoc, x.inv_hom, AugHom.ident_comp]

set_option backward.isDefEq.respectTransparency false in
include unit_eq mi h j unit_middle in
/-- The canonical resource-occurrence word is an executable test of the
permutation hypothesis, even when several data leaves are equal. -/
theorem StructuralPath.coherent_of_tag_word {a b : Tree} (p q : StructuralPath a b)
    (law : FubiniTreeLaws R J P m)
    (tags : (p.tagTransport (tagsFrom 0 a)).target.expr.leaves =
      (q.tagTransport (tagsFrom 0 a)).target.expr.leaves) :
    (pIso p).hom = (pIso q).hom ∧ (jIso p).hom = (jIso q).hom := by
  let s := tagsFrom 0 a
  let hn := tagsFrom_nodup a 0
  have ht := Tagging.eq_of_leaves (p.tagTransport s).target (q.tagTransport s).target tags
  exact ⟨p.separate_coherent M R L J N NR NL Q U hl hr ia is iu su unit_eq q s hn ht,
    p.joint_coherent M R L J N NR NL Q U hl hr ia is iu su unit_eq m mi h j unit_middle q law s hn ht⟩

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
