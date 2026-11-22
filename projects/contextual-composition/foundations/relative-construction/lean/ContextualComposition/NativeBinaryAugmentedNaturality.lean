module
public import ContextualComposition.NativeBinaryRawProduct
public import ContextualComposition.BinaryAugmentedSquareBridge
@[expose] public section

/-! The original binary comparison is natural on actual independently
assembled augmented arrows in the addressed ordered inputs. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

structure BinaryNativeAugSquare {I : C} {A B A' B' : Aug ℙ I}
    (e : NativeAugmentedIso A A') (d : NativeAugmentedIso B B')
    (p : Hom ℙ A.base B.base) (q : Hom ℙ A'.base B'.base) where
  separate : AugHom ℙ A B
  joint : AugHom ℙ A' B'
  separate_native : separate.native = p
  joint_native : joint.native = q
  commutes : separate.comp d.hom = e.hom.comp joint

variable {T : Bi (coeff (C:=C))}
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable {I : C} (J : UnitCompat R I) (m : Middle T I)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- The literal augmented binary square. Both horizontal maps retain
exactly their original native components. No functor laws are asserted. -/
noncomputable def actual_binary_augmented_square
    (N : GridBinary (symmetricCross (C:=C)) R L)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (hx : (dependentWord xs' us').Nodup) (hy : (dependentWord ys' vs').Nodup)
    (h₀ : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    (h₁ : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A us) x ⟶ I)
    (η : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B vs) y ⟶ I)
    (δ' : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A' us') x ⟶ I)
    (η' : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B' vs') y ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (γ : fold 𝒮 Zₐ P ys ⟶ I)
    (ε' : fold 𝒮 Zₐ V' xs' ⟶ I) (γ' : fold 𝒮 Zₐ P' ys' ⟶ I)
    (hp : (origDependentWordMap D R L hx).comp (dependentWordAug R L J xs' us' V' A' δ' ε').ε =
      (dependentWordAug R L J xs us V A δ ε).ε)
    (hq : (origDependentWordMap E R L hy).comp (dependentWordAug R L J ys' vs' P' B' η' γ').ε =
      (dependentWordAug R L J ys vs P B η γ).ε)
    (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    BinaryNativeAugSquare
      (binaryNativeAugIso xs ys us vs V P A B R L N NR NL J m δ η ε γ mi h₀ h j unit_middle)
      (binaryNativeAugIso xs' ys' us' vs' V' P' A' B' R L N NR NL J m δ' η' ε' γ' mi h₁ h j unit_middle)
      (separateBinaryMap D E R L h₁) (jointBinaryMap D E R L h₁) := by
  let e := binaryNativeAugIso xs ys us vs V P A B R L N NR NL J m δ η ε γ mi h₀ h j unit_middle
  let d := binaryNativeAugIso xs' ys' us' vs' V' P' A' B' R L N NR NL J m δ' η' ε' γ' mi h₁ h j unit_middle
  let p := separateBinaryMap D E R L h₁
  let q := jointBinaryMap D E R L h₁
  let S₀ := wordAug (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves
    (separateWordAug xs ys us vs V P A B R L J δ η ε γ)
  let S₁ := wordAug (separateLeafLabels (T:=T) V' P' A' B') (fourOccurrenceExpr xs' ys' us' vs').leaves
    (separateWordAug xs' ys' us' vs' V' P' A' B' R L J δ' η' ε' γ')
  let H : AugHom ℙ S₀ S₁ := ⟨p, separateBinary_preserves D E R L J N NR NL _hl _hr hx hy h₀ h₁
    δ η δ' η' ε γ ε' γ' hp hq⟩
  have s : H.native.comp d.hom.native = e.hom.native.comp q :=
    actual_binary_native_square D E R L N NR NL m mi h₀ h₁ h j
  exact ⟨H, e.lift_square d H q s, rfl, rfl, e.lift_square_commutes d H q s⟩


theorem dependentWord_nodup {X U : Type u} {xs : List X} {us : X → List U}
    (hx : xs.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup) :
    (dependentWord xs us).Nodup := by
  rw [← dependentExpr_leaves]
  unfold dependentExpr
  apply GridExpr.nodup_over _ xs hx
  · intro x h
    rw [leafWord_pin]
    exact List.Pairwise.map (Prod.mk x) (fun _ _ ne e => ne (congrArg Prod.snd e)) (hu x h)
  · intro x _ y _ e a ha hb
    rw [leafWord_pin] at ha hb
    obtain ⟨p,_,ep⟩ := List.mem_map.mp ha
    obtain ⟨q,_,eq⟩ := List.mem_map.mp hb
    exact e (congrArg Prod.fst (ep.trans eq.symm))

theorem occurrenceWord_nodup
    (hx : (dependentWord xs us).Nodup) (hy : (dependentWord ys vs).Nodup) :
    (fourOccurrenceExpr xs ys us vs).leaves.Nodup := by
  rw [← nativeOccurrenceExpr_word_product]
  exact List.Pairwise.map pairQuad (fun _ _ ne e => ne (pairQuad_injective e)) (nodup_product_word hx hy)

set_option backward.isDefEq.respectTransparency false in
/-- The unary premises for the binary lift follow from preservation of
the literal parent and continuation inputs and distinct addressed rows. -/
theorem unaryPreserves_of_orderedInputs
    [DecidableEq X]
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (_hl : ∀ a : C, SameLeftGather T a L)
    (h₀ : xs.Nodup) (h₁ : xs'.Nodup)
    (ha : ∀ x ∈ xs, (us x).Nodup) (ha' : ∀ x ∈ xs', (us' x).Nodup)
    {δ : ∀ x, fold 𝒮 Zₐ (A x) (us x) ⟶ I}
    {δ' : ∀ x, fold 𝒮 Zₐ (A' x) (us' x) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (hp : D.Preserves h₁ (fun x hx => ha' (D.parent x) (D.parent_mem x hx)) δ δ' ε ε') :
    (origDependentWordMap D R L (dependentWord_nodup h₁ ha')).comp
      (dependentWordAug R L J xs' us' V' A'
        (fun x => eqToHom (std_fold_map id (A' x) (us' x)) ≫ δ' x) ε').ε =
    (dependentWordAug R L J xs us V A
      (fun x => eqToHom (std_fold_map id (A x) (us x)) ≫ δ x) ε).ε := by
  let h := dependentWord_nodup h₁ ha'
  let k := dependentWord_nodup h₀ ha
  have hw (j : Fin xs'.length) : (selectedBlockWord D xs'[j]).Nodup := by
    have z : (wordFibre (dependentWord xs us) (D.parent ∘ Prod.fst) xs'[j]).Nodup := k.filter _
    rw [← selectedBlockWord_map D xs'[j]] at z
    exact List.Pairwise.of_map (dependentSliceRelabel D xs'[j])
      (fun _ _ ne e => ne (congrArg (dependentSliceRelabel D xs'[j]) e)) z
  let _ : ∀ x : X, (leftFactor T (V x)).LaxBraided := fun x => lF _
  exact (origDependentWordAugMap D R L N NL J hp h k h₀
    (fun j => ha' xs'[j] (List.getElem_mem _))
    (fun _ x => ha x.val x.property.1) hw (fun x => _hl _)).preserves


variable {Y W Y' W' : Type u}
variable [DecidableEq Y'] [DecidableEq W']
variable {ys : List Y} {vs : Y → List W} {ys' : List Y'} {vs' : Y' → List W'}
variable {P : Y → C} {B : Y → W → C} {P' : Y' → C} {B' : Y' → W' → C}
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')

/-- Reindex a raw continuation-fold augmentation into the historical
coefficient-valued list without changing the specified native map. -/
def indexedAugmentation {X U : Type u} {B : X → U → C} {us : X → List U}
    {I : C} (δ : ∀ x, fold 𝒮 Zₐ (B x) (us x) ⟶ I) :
    ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput B us) x ⟶ I :=
  fun x => eqToHom (std_fold_map id (B x) (us x)) ≫ δ x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- The binary augmented comparison on literal variation of the parent
and every continuation, with leaf-address and selected-fibre conditions
derived from distinct parent addresses and distinct local child addresses. -/
noncomputable def actual_binary_augmented_square_of_orderedInputs
    [DecidableEq X] [DecidableEq Y]
    (N : GridBinary (symmetricCross (C:=C)) R L)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (hx : xs.Nodup) (hy : ys.Nodup) (hx' : xs'.Nodup) (hy' : ys'.Nodup)
    (ha : ∀ x ∈ xs, (us x).Nodup) (hb : ∀ y ∈ ys, (vs y).Nodup)
    (ha' : ∀ x ∈ xs', (us' x).Nodup) (hb' : ∀ y ∈ ys', (vs' y).Nodup)
    {δ : ∀ x, fold 𝒮 Zₐ (A x) (us x) ⟶ I} {η : ∀ y, fold 𝒮 Zₐ (B y) (vs y) ⟶ I}
    {δ' : ∀ x, fold 𝒮 Zₐ (A' x) (us' x) ⟶ I} {η' : ∀ y, fold 𝒮 Zₐ (B' y) (vs' y) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {γ : fold 𝒮 Zₐ P ys ⟶ I}
    {ε' : fold 𝒮 Zₐ V' xs' ⟶ I} {γ' : fold 𝒮 Zₐ P' ys' ⟶ I}
    (hp : D.Preserves hx' (fun x h => ha' (D.parent x) (D.parent_mem x h)) δ δ' ε ε')
    (hq : E.Preserves hy' (fun y h => hb' (E.parent y) (E.parent_mem y h)) η η' γ γ')
    (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    let src := occurrenceWord_nodup (dependentWord_nodup hx ha) (dependentWord_nodup hy hb)
    let dst := occurrenceWord_nodup (dependentWord_nodup hx' ha') (dependentWord_nodup hy' hb')
    BinaryNativeAugSquare
      (binaryNativeAugIso xs ys us vs V P A B R L N NR NL J m
        (indexedAugmentation δ) (indexedAugmentation η) ε γ mi src h j unit_middle)
      (binaryNativeAugIso xs' ys' us' vs' V' P' A' B' R L N NR NL J m
        (indexedAugmentation δ') (indexedAugmentation η') ε' γ' mi dst h j unit_middle)
      (separateBinaryMap D E R L dst) (jointBinaryMap D E R L dst) := by
  intro src dst
  have pd := unaryPreserves_of_orderedInputs D R L J N NL _hl hx hx' ha ha' hp
  have pe := unaryPreserves_of_orderedInputs E R L J N NL _hl hy hy' hb hb' hq
  exact actual_binary_augmented_square D E R L J m N NR NL _hl _hr
    (dependentWord_nodup hx' ha') (dependentWord_nodup hy' hb') src dst
    (indexedAugmentation δ) (indexedAugmentation η) (indexedAugmentation δ') (indexedAugmentation η')
    ε γ ε' γ' pd pe mi h j unit_middle

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
