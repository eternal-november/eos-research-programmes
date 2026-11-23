module
public import ContextualComposition.NativeIndependentSingletonTrace
public import ContextualComposition.NativeFubiniStructuralLaws
@[expose] public section

/-! Positional and coefficient trace of the actual binary Fubini
augmentation comparison, with no requirement that its addressed
shuffle preserve the chosen enumerations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {T : Bi (coeff (C:=C))} {I : C}
variable {X U Y W : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (A x) (us x) ⟶ I)
variable (η : ∀ y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B y) (vs y) ⟶ I)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) P ys ⟶ I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
local notation "depA" => dependentLabels (T:=T) V A
local notation "depB" => dependentLabels (T:=T) P B
local notation "depAB" => dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B)
local notation "wA" => dependentWord xs us
local notation "wB" => dependentWord ys vs
local notation "wAB" => dependentWord (xs.product ys) (crossChildWord us vs)
local notation "leafA" => separateLeafLabels (T:=T) V P A B
local notation "leafB" => jointLeafLabels (T:=T) V P A B

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
theorem binaryProductAugIso_trace
    (hx : (wA).Nodup) (hy : (wB).Nodup) (hz : (wAB).Nodup)
    (hn : (fourOccurrenceExpr xs ys us vs).leaves.Nodup) :
    let F := ((rawWordFrame depA wA hx).tensor T (rawWordFrame depB wB hy)).relabel
      pairQuad pairQuad_injective leafA (fun _ => rfl)
    let G := (rawWordFrame depAB wAB hz).relabel
      (jointPairRetag (X:=X) (U:=U) (Y:=Y) (W:=W)) (jointPairRetag.injective) leafB (fun _ => rfl)
    RawSingletonTrace F G (fun z => m.cell (V z.1) (A z.1 z.2.1) (P z.2.2.1) (B z.2.2.1 z.2.2.2))
      (binaryProductAugIso R L J xs ys us vs V P A B δ η ε γ N NR NL m mi h j unit_middle hl hr hn).hom.native := by
  intro F G
  let s := (fourOccurrenceExpr xs ys us vs).leaves
  let t := (fourJointExpr xs ys us vs).leaves
  let r := quadRead wA wB
  let u := independentWord (wordFamily depA wA) (wordFamily depB wB)
  let f := jointPairRetag (X:=X) (U:=U) (Y:=Y) (W:=W)
  let q := gridOrder (fourExchangeChart xs ys us vs)
  let α := binaryLeafIso V P A B m mi
  let e := binaryNativeAugIso xs ys us vs V P A B R L N NR NL J m
    (indexedAugmentation δ) (indexedAugmentation η) ε γ mi hn h j unit_middle
  let e' := binaryProductAugIso R L J xs ys us vs V P A B δ η ε γ N NR NL m mi h j unit_middle hl hr hn
  have ht : t.Nodup := q.perm.nodup_iff.mp hn
  let F₀ := rawWordFrame leafA s hn
  let G₀ := rawWordFrame leafB t ht
  have h₀ : RawSingletonTrace F₀ G₀ (fun z => (α z).hom) e.hom.native := by
    unfold e binaryNativeAugIso
    exact wordAugIso_trace _ _ q hn ht α _ _ _
  have e₀ : independentFamily T (wordFamily depA wA) (wordFamily depB wB) = wordFamily leafA s :=
    wordFamily_read_eq leafA r u s (quadRead_word xs ys us vs)
  have e₁ : wordFamily depAB wAB = wordFamily leafB t :=
    wordFamily_read_eq leafB f wAB t (jointPairRetag_word xs ys us vs)
  have readF (i : Fin (independentFamily T (wordFamily depA wA) (wordFamily depB wB)).n) :
      F.read i = F₀.read (Fin.cast (congrArg Family.n e₀) i) :=
    rawWordFrame_read_cast leafA r u s (quadRead_word xs ys us vs) i
  have readG (i : Fin (wordFamily depAB wAB).n) :
      G.read i = G₀.read (Fin.cast (congrArg Family.n e₁) i) :=
    rawWordFrame_read_cast leafB f wAB t (jointPairRetag_word xs ys us vs) i
  have e₂ : HEq e.hom.native e'.hom.native := by
    unfold e' binaryProductAugIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact h₀.retarget e₀.symm e₁.symm e₂
    (rawFrame_read_reverse F F₀ e₀ readF) (rawFrame_read_reverse G G₀ e₁ readG) (fun _ => HEq.rfl)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
