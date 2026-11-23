module
public import ContextualComposition.NativeFubiniTreeCircuitTrace
@[expose] public section

/-! Exact circuit certificates for the three independently constructed
native root arrows in a standard symmetric multiplicative interpretation. -/
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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4500000 in
noncomputable def assocRootCircuitTrace (a b c : Tree)
    (s : Tagging Tag a) (t : Tagging Tag b) (u : Tagging Tag c) :
    CircuitTrace M R L J ((AssocMove.root a b c).tagForward (.fork (.fork s t) u))
      (separateAssoc P R L J NR NL Q U hl hr ia a b c).hom.native where
  coefficient z := αₘ (lc a z.1.1) (lc b z.1.2) (lc c z.2)
  trace := by
    let e := tripleRetag (X:=a.Address) (Y:=b.Address) (W:=c.Address)
    let F := fr (.fork (.fork a b) c)
    let G := fr (.fork a (.fork b c))
    let p (z : (a.Address × b.Address) × c.Address) := (αₘ (lc a z.1.1) (lc b z.1.2) (lc c z.2)).hom
    have h := separateAssoc_trace P R L J NR NL Q U hl hr ia a b c
    have s := h.relabel e.symm e.symm.injective F.label (G.label ∘ e) (fun _ => rfl)
      (fun z => congrArg G.label (e.apply_symm_apply z).symm) p (fun _ => HEq.rfl)
    exact s.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  values V z hz := (AssocMove.root a b c).tagForward_matches V (.fork (.fork s t) u) z hz
  circuit_eval V z hz := by
    have e := (Tagging.matches_eval V 𝕄 a s z.1.1 hz.1.1).symm
    have f := (Tagging.matches_eval V 𝕄 b t z.1.2 hz.1.2).symm
    have g := (Tagging.matches_eval V 𝕄 c u z.2 hz.2).symm
    exact assoc_cell_heq P e f g

set_option backward.isDefEq.respectTransparency false in
noncomputable def swapRootCircuitTrace (a b : Tree) (s : Tagging Tag a) (t : Tagging Tag b) :
    CircuitTrace M R L J ((StructuralMove.swap a b).tagForward (.fork s t))
      (separateSwapIso P R L J N Q su is a b).hom.native where
  coefficient z := βₘ (lc a z.1) (lc b z.2)
  trace := separateSwap_trace P R L J N Q su is a b
  values V z hz := (StructuralMove.swap a b).tagForward_matches V (.fork s t) z hz
  circuit_eval V z hz := by
    have e := (Tagging.matches_eval V 𝕄 a s z.1 hz.1).symm
    have f := (Tagging.matches_eval V 𝕄 b t z.2 hz.2).symm
    exact swap_cell_heq P e f

set_option backward.isDefEq.respectTransparency false in
include unit_eq in
noncomputable def runitRootCircuitTrace (a : Tree) (s : Tagging Tag a) :
    CircuitTrace M R L J ((StructuralMove.eraseRight a).tagForward (.fork s .unit))
      (separateRightUnitIso R L J hl iu a).hom.native where
  coefficient z := ρₘ (lc a z.1)
  trace := by
    have t := separateRightUnit_trace R L J hl iu a
    exact t.changeFrame (fun _ => rfl) (fun _ => rfl)
      (fun z => heq_of_eq (unit_eq (lc a z.1)))
  values V z hz := (StructuralMove.eraseRight a).tagForward_matches V (.fork s .unit) z hz
  circuit_eval V z hz := by
    have e := (Tagging.matches_eval V 𝕄 a s z.1 hz.1).symm
    have h {a b : C} (p : a = b) : HEq (ρₘ a).hom (ρₘ b).hom := by subst b; rfl
    exact h e

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
