module
public import ContextualComposition.NativeFubiniDependentAssocTree
public import ContextualComposition.NativeAdmissibleFubiniPathCoherence
public import ContextualComposition.ContextualRigAdapter
@[expose] public section

/-! A source-facing local distributor interface for the native calculus:
two genuine symmetric monoidal structures, natural invertible binary
distributors and absorptions, and explicit local compatibility laws.
No finite coherence, augmentation, or Fubini law is a field. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open DependentFubiniTree
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [add : MonoidalCategory C] [sa : SymmetricCategory C]
local notation "S" => Additive.ofBraided (C:=C)
variable (M : TensorSemantics C)
set_option quotPrecheck false in
local notation "Iₘ" => @MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct
set_option quotPrecheck false in
local notation "rho" => fun a => (@MonoidalCategoryStruct.rightUnitor C cat M.tensor.toMonoidalCategoryStruct a).hom
set_option quotPrecheck false in
local notation "P" => @tensorPrimitives C cat M.tensor M.symmetric.toBraidedCategory
set_option quotPrecheck false in
local notation "m" => additiveMiddle (@Additive.ofBraided C cat M.tensor M.symmetric.toBraidedCategory)

set_option quotPrecheck false in
local notation "mul" => @Binary.ofMonoidal C cat M.tensor

structure NativeRigGrid where
  leftSplit (a : C) : Split S ((mul).left a)
  rightDist (a b : C) : (mul).left ((S).sum.obj a b) ≅ (S).pointwise ((mul).left a) ((mul).left b)
  absorbLeft : (mul).left (S).zero ≅ (S).zeroFunctor
  rightDist_preserves (a b : C) :
    PreservesSplit (leftSplit _) ((leftSplit a).pointwise (leftSplit b)) (rightDist a b).hom
  absorbLeft_preserves : PreservesSplit (leftSplit _) (S).zeroSplit absorbLeft.hom

abbrev NativeRigGrid.toGrid (D : NativeRigGrid M) : GridData S :=
  ⟨mul, D.leftSplit, D.rightDist, D.absorbLeft, D.rightDist_preserves, D.absorbLeft_preserves⟩

/-- Constructor of the source rig datum. Each law here applies only to
the binary or nullary distributor generators or to the structural
multiplicative maps in a single additive argument. -/
structure NativeRigLocalLaws (D : NativeRigGrid M) : Prop where
  natural : GridNatural (D.toGrid M)
  leftContext (a : C) : AdditiveContextLaws (Lin.left (leftGather (D.toGrid M)) a)
  rightContext (a : C) : AdditiveContextLaws (Lin.right (gather (D.toGrid M)) a)
  primitive : ForwardPrimitive (gather (D.toGrid M)) (leftGather (D.toGrid M)) P
  rightUnit_zero : (gather (D.toGrid M)).nil Iₘ ≫ rho (𝟙_ C) = 𝟙 (𝟙_ C)
  rightUnit_bin (a b : C) : (gather (D.toGrid M)).cons a b Iₘ ≫ rho (a ⊗ b) =
    rho a ⊗ₘ rho b

/-- Bundles local source generator laws, not any finite conclusion. -/
structure CoherentNativeRig where
  chart : NativeRigGrid M
  laws : NativeRigLocalLaws M chart

namespace CoherentNativeRig
variable (K : CoherentNativeRig M)
set_option quotPrecheck false in
local notation "Tₘ" => binary (@Binary.ofMonoidal C cat M.tensor)

abbrev rightGather : Gather (binary (S).sum) Tₘ (S).zero :=
  gather (K.chart.toGrid M)

abbrev leftGathering : LeftGather (binary (S).sum) Tₘ (S).zero :=
  leftGather (K.chart.toGrid M)

set_option quotPrecheck false in
local notation "R" => rightGather M K
set_option quotPrecheck false in
local notation "L" => leftGathering M K

theorem gridBinary : GridBinary (symmetricCross (C:=C)) R L :=
  cross_binary (K.chart.toGrid M) add_middle_involutive

theorem right_natural : GatherOuterNat R :=
  gatherOuter (K.chart.toGrid M) K.laws.natural

theorem left_natural : GatherLeftNat L :=
  leftGatherNatural (K.chart.toGrid M) K.laws.natural

theorem rightContext (a : C) : AdditiveContextLaws (Lin.right R a) :=
  K.laws.rightContext a

theorem leftContext (a : C) : AdditiveContextLaws (Lin.left L a) :=
  K.laws.leftContext a

abbrev leftLax (a : C) : (leftFactor Tₘ a).LaxBraided :=
  linLax (Lin.left L a) (K.leftContext M a)

abbrev rightLax (a : C) : (rightFactor (T:=Tₘ) a).LaxBraided :=
  linLax (Lin.right R a) (K.rightContext M a)

set_option linter.style.haveILetI false in
theorem leftSame (a : C) :
    letI := K.leftLax M a
    SameLeftGather Tₘ a L :=
  ⟨rfl, fun _ _ => rfl⟩

set_option linter.style.haveILetI false in
theorem rightSame (a : C) :
    letI := K.rightLax M a
    SameRightGather R a :=
  ⟨rfl, fun _ _ => rfl⟩

abbrev unit : UnitCompat R Iₘ :=
  @multiplicativeUnit C cat M.tensor (binary (S).sum) (S).zero R K.laws.rightUnit_zero K.laws.rightUnit_bin

theorem primitive : PrimitiveLinearity R L P :=
  ForwardPrimitive.upgrade R L P K.laws.primitive (fun a b c =>
    (@MonoidalCategoryStruct.associator C cat M.tensor.toMonoidalCategoryStruct a b c).hom_inv_id)
    (fun a b c => (@MonoidalCategoryStruct.associator C cat M.tensor.toMonoidalCategoryStruct a b c).inv_hom_id)

theorem medialLinear : MedialLinear m R L ∧ MedialInner m R L :=
  @braided_middle_linear C cat M.tensor M.symmetric.toBraidedCategory (binary (S).sum) (S).zero
    R L K.laws.primitive (K.right_natural M) (K.left_natural M)

set_option linter.style.haveILetI false in
theorem associatorUnit : AssocRightUnit R (K.unit M) P := by
  intro a b
  letI := M.tensor
  change (α_ a b (𝟙_ C)).hom ≫ (𝟙 a ⊗ₘ (ρ_ b).hom) = (ρ_ (a ⊗ b)).hom
  rw [id_tensorHom]
  monoidal

omit add sa in
theorem associator_isIso (a b c : C) : IsIso ((P).assoc a b c) :=
  inferInstanceAs (IsIso ((@MonoidalCategoryStruct.associator C cat M.tensor.toMonoidalCategoryStruct a b c).hom))

omit add sa in
theorem swap_isIso (a b : C) : IsIso ((P).swap a b) :=
  inferInstanceAs (IsIso ((@BraidedCategory.braiding C cat M.tensor M.symmetric.toBraidedCategory a b).hom))

theorem unit_isIso (a : C) : IsIso ((K.unit M).ρ a) :=
  inferInstanceAs (IsIso (rho a))

set_option linter.style.haveILetI false in
theorem swapUnit : (P).swap Iₘ Iₘ ≫ (K.unit M).ρ Iₘ = (K.unit M).ρ Iₘ := by
  letI := M.tensor
  letI := M.symmetric
  change (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
  rw [braiding_rightUnitor]
  monoidal

set_option linter.style.haveILetI false in
theorem unitMiddle : (m).cell Iₘ Iₘ Iₘ Iₘ ≫ unitCollapse R (K.unit M) = unitCollapse R (K.unit M) := by
  letI := M.tensor
  letI := M.symmetric
  have q : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal
  have h : (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
    rw [braiding_tensorUnit_left, q, Iso.hom_inv_id]
  have h' : tensorμ (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) = 𝟙 _ := by
    unfold tensorμ
    rw [h]
    monoidal
  change tensorμ (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) ≫ _ = _
  rw [h', Category.id_comp]

theorem treeLaws : FubiniTreeLaws R (K.unit M) P m :=
  standardFubiniTreeLaws M.tensor M.symmetric R (K.unit M) (fun _ => rfl)

open IndexedNativeFamily
variable {A : Type u} (projCls : NativeProjectionClass.{u})
set_option quotPrecheck false in
local notation "J" => K.unit M
set_option quotPrecheck false in
local notation "G" => K.gridBinary M
set_option quotPrecheck false in
local notation "NR" => K.right_natural M
set_option quotPrecheck false in
local notation "NL" => K.left_natural M
set_option quotPrecheck false in
local notation "hl" => K.leftSame M
set_option quotPrecheck false in
local notation "hr" => K.rightSame M
set_option quotPrecheck false in
local notation "mi" => additiveMiddleInv (@Additive.ofBraided C cat M.tensor M.symmetric.toBraidedCategory)

set_option backward.isDefEq.respectTransparency false in
noncomputable def fubini (n : Nat) (D : Fin n → AdmissibleDependentInput projCls A Iₘ) :
    nativeFubiniSeparate R L J projCls n D ≅ nativeFubiniJoint R L J projCls n D := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := K.unit_isIso M Iₘ
  exact nativeAdmissibleFubini R L J projCls G NR NL hl hr m mi
    (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M) n D

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateMap (n : Nat) {D E : Fin n → AdmissibleDependentInput projCls A Iₘ}
    (p : ∀ i, AdmissibleDependentArrow (D i) (E i)) :
    nativeFubiniSeparate R L J projCls n D ⟶ nativeFubiniSeparate R L J projCls n E := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact nativeFubiniSeparateMap R L J projCls G NR NL hl hr n p

set_option backward.isDefEq.respectTransparency false in
noncomputable def jointMap (n : Nat) {D E : Fin n → AdmissibleDependentInput projCls A Iₘ}
    (p : ∀ i, AdmissibleDependentArrow (D i) (E i)) :
    nativeFubiniJoint R L J projCls n D ⟶ nativeFubiniJoint R L J projCls n E := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact nativeFubiniJointMap R L J projCls G NR NL hl hr n p

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem fubini_natural (n : Nat) {D E : Fin n → AdmissibleDependentInput projCls A Iₘ}
    (p : ∀ i, AdmissibleDependentArrow (D i) (E i)) :
    K.separateMap M projCls n p ≫ (K.fubini M projCls n E).hom =
      (K.fubini M projCls n D).hom ≫ K.jointMap M projCls n p := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := K.unit_isIso M Iₘ
  exact nativeAdmissibleFubini_natural R L J projCls G NR NL hl hr m mi
    (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M) n p

set_option backward.isDefEq.respectTransparency false in
noncomputable def accumulation :
    NativeDependentPair Iₘ ⥤ Aug (standardPush (C:=C)) Iₘ := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact nativeAccumulationFunctor R L J G NR NL hl hr

section IndexedPath
open IndexedNativeFamily.AdmissibleFubiniTree
variable {projCls}
set_option quotPrecheck false in
local notation "QT" => K.primitive M
set_option quotPrecheck false in
local notation "UT" => K.associatorUnit M
set_option quotPrecheck false in
local notation "IA" => associator_isIso M
set_option quotPrecheck false in
local notation "IS" => swap_isIso M
set_option quotPrecheck false in
local notation "IU" => K.unit_isIso M
set_option quotPrecheck false in
local notation "SU" => K.swapUnit M

set_option backward.isDefEq.respectTransparency false in
noncomputable def treeFubini (a : AdmissibleFubiniTree projCls A Iₘ) :
    a.separateDisplay R L J ≅ a.jointDisplay R L J := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := IU Iₘ
  exact a.comparison R L J G NR NL hl hr m mi (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M)

set_option backward.isDefEq.respectTransparency false in
noncomputable def treePathSeparate {a b : AdmissibleFubiniTree projCls A Iₘ}
    (p : ∀ x : A, StructuralPath (a.eval x) (b.eval x)) :
    a.separateDisplay R L J ≅ b.separateDisplay R L J := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact pathSeparateIso R L J G NR NL hl hr P QT UT IA SU IS IU p

set_option backward.isDefEq.respectTransparency false in
noncomputable def treePathJoint {a b : AdmissibleFubiniTree projCls A Iₘ}
    (p : ∀ x : A, StructuralPath (a.eval x) (b.eval x)) :
    a.jointDisplay R L J ≅ b.jointDisplay R L J := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact pathJointIso R L J G NR NL hl hr P QT UT IA SU IS IU p

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem treePath_fubini {a b : AdmissibleFubiniTree projCls A Iₘ}
    (p : ∀ x : A, StructuralPath (a.eval x) (b.eval x)) :
    (K.treePathSeparate M p).hom ≫ (K.treeFubini M b).hom =
      (K.treeFubini M a).hom ≫ (K.treePathJoint M p).hom := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact path_fubini R L J G NR NL hl hr m mi (K.medialLinear M).1 (K.medialLinear M).2
    (K.unitMiddle M) P QT UT IA SU IS IU p (K.treeLaws M)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem treePath_coherent {a b : AdmissibleFubiniTree projCls A Iₘ}
    (p q : ∀ x : A, StructuralPath (a.eval x) (b.eval x))
    (tags : ∀ x, ((p x).tagTransport (tagsFrom 0 (a.eval x))).target.expr.leaves =
      ((q x).tagTransport (tagsFrom 0 (a.eval x))).target.expr.leaves) :
    (K.treePathSeparate M p).hom = (K.treePathSeparate M q).hom ∧
    (K.treePathJoint M p).hom = (K.treePathJoint M q).hom := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact path_coherent_of_tag_word M R L J G NR NL QT UT hl hr IA IS IU SU (fun _ => rfl)
    m mi (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M) p q (K.treeLaws M) tags

set_option backward.isDefEq.respectTransparency false in
noncomputable def mixedLeft (d : DependentThirdTree Iₘ) :
    NativeAugmentedIso ((d.leftTree R L J).separate R L J)
      ((d.third R L J).leftData R L J |>.accumulate R L J) := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := IU Iₘ
  exact d.leftMixed R L J G NR NL hl hr m mi (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M)

set_option backward.isDefEq.respectTransparency false in
noncomputable def mixedRight (d : DependentThirdTree Iₘ) :
    NativeAugmentedIso ((d.rightTree R L J).separate R L J)
      ((d.third R L J).rightData R L J |>.accumulate R L J) := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := IU Iₘ
  exact d.rightMixed R L J G NR NL hl hr m mi (K.medialLinear M).1 (K.medialLinear M).2 (K.unitMiddle M)

set_option backward.isDefEq.respectTransparency false in
noncomputable def mixedSeparateAssoc (d : DependentThirdTree Iₘ) :
    NativeAugmentedIso ((d.leftTree R L J).separate R L J) ((d.rightTree R L J).separate R L J) := by
  letI := K.leftLax M
  letI := K.rightLax M
  exact d.separateAssoc R L J P G NR NL QT UT hl hr IA

set_option backward.isDefEq.respectTransparency false in
noncomputable def mixedJointAssoc (d : DependentThirdTree Iₘ) :
    NativeAugmentedIso ((d.third R L J).leftData R L J |>.accumulate R L J)
      ((d.third R L J).rightData R L J |>.accumulate R L J) := by
  letI := K.leftLax M
  exact (d.third R L J).associator R L J P NL QT UT hl IA

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem mixed_coherent (d : DependentThirdTree Iₘ) :
    (K.mixedLeft M d).hom.comp (K.mixedJointAssoc M d).hom =
      (K.mixedSeparateAssoc M d).hom.comp (K.mixedRight M d).hom := by
  letI := K.leftLax M
  letI := K.rightLax M
  letI := IU Iₘ
  exact d.mixed_coherent R L J P G NR NL QT UT hl hr IA m mi (K.medialLinear M).1 (K.medialLinear M).2
    (K.unitMiddle M) (standardMedialDependentAssoc M.tensor M.symmetric.toBraidedCategory)

end IndexedPath

end CoherentNativeRig

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
