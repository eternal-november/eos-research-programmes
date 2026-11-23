module
public import ContextualComposition.NativeIndependentTripleCell
@[expose] public section

/-! The actual independent augmented associator. Both endpoints are
literal iterates of the independent product; the comparison acts on
each exact triple address by the supplied tensor associator. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (P : TensorPrimitive T)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P)
variable (U : AssocRightUnit R J P)
variable {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (r : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D ws ⟶ I)

def independentUnitMergeLeft : T.obj (T.obj I I) I ⟶ I :=
  T.map (J.ρ I) (𝟙 I) ≫ J.ρ I
def independentUnitMergeRight : T.obj I (T.obj I I) ⟶ I :=
  T.map (𝟙 I) (J.ρ I) ≫ J.ρ I

set_option backward.isDefEq.respectTransparency false in
include U in
theorem independentUnit_associative :
    independentUnitMergeLeft R J = P.assoc I I I ≫ independentUnitMergeRight R J := by
  unfold independentUnitMergeLeft independentUnitMergeRight
  have h : P.assoc I I I ≫ T.map (𝟙 I) (J.ρ I) = J.ρ (T.obj I I) := U I I
  have k : T.map (J.ρ I) (𝟙 I) ≫ J.ρ I = J.ρ (T.obj I I) ≫ J.ρ I := J.natural (J.ρ I)
  rw [reassoc_of% h, k]

def independentAssocLeftAug :=
  rectangularWordAugCell R L (J.ρ I) (crossLabel T A B) D (xs.product ys) ws
    (rectangularWordAugCell R L (J.ρ I) A B xs ys p q) r

def independentAssocRightAug :=
  rectangularWordAugCell R L (J.ρ I) A (crossLabel T B D) xs (ys.product ws) p
    (rectangularWordAugCell R L (J.ρ I) B D ys ws q r)

set_option backward.isDefEq.respectTransparency false in
theorem independentAssocLeftAug_flat :
    independentAssocLeftAug R L J A B D xs ys ws p q r =
      tripleIndependentLeftCell R L A B D xs ys ws p q r ≫ independentUnitMergeLeft R J := by
  let V := crossLabel T A B
  let e := rectWordChart V xs ys ≫ independentCell R L A B xs ys p q
  have h : T.map (e ≫ J.ρ I) r =
      T.map e r ≫ T.map (J.ρ I) (𝟙 I) := by
    rw [bi_map_comp, Category.comp_id]
  unfold independentAssocLeftAug rectangularWordAugCell tripleIndependentLeftCell independentUnitMergeLeft
  simp only [independentCell, Category.assoc]
  have e' : rectWordChart V xs ys ≫ rowGather R L A B xs ys ≫ T.map p q ≫ J.ρ I = (e ≫ J.ρ I) := by
    unfold e independentCell
    simp only [Category.assoc]
  rw [e', h, Category.assoc]
  simp only [e, independentCell]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem independentAssocRightAug_flat :
    independentAssocRightAug R L J A B D xs ys ws p q r =
      tripleIndependentRightCell R L A B D xs ys ws p q r ≫ independentUnitMergeRight R J := by
  let V := crossLabel T B D
  let e := rectWordChart V ys ws ≫ independentCell R L B D ys ws q r
  have h : T.map p (e ≫ J.ρ I) =
      T.map p e ≫ T.map (𝟙 I) (J.ρ I) := by
    rw [bi_map_comp, Category.comp_id]
  unfold independentAssocRightAug rectangularWordAugCell tripleIndependentRightCell independentUnitMergeRight
  simp only [independentCell, Category.assoc]
  have e' : rectWordChart V ys ws ≫ rowGather R L B D ys ws ≫ T.map q r ≫ J.ρ I = (e ≫ J.ρ I) := by
    unfold e independentCell
    simp only [Category.assoc]
  rw [e', h, Category.assoc]
  simp only [e, independentCell]
  rfl

set_option backward.isDefEq.respectTransparency false in
include NR NL Q U in
theorem independentAssocAug_heq
    [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c) :
    HEq (independentAssocLeftAug R L J A B D xs ys ws p q r)
      (act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)) (xs.product (ys.product ws)) ≫
        independentAssocRightAug R L J A B D xs ys ws p q r) := by
  let H := crossLabel T (crossLabel T A B) D
  let G := H ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
  let v := (xs.product ys).product ws
  let w := xs.product (ys.product ws)
  let e := (std_fold_map G tripleRetag v).symm.trans
    (congrArg (fold 𝒮 Zₐ G) (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)))
  let s := tripleIndependentLeftCell R L A B D xs ys ws p q r
  let t := tripleIndependentRightCell R L A B D xs ys ws p q r
  let α := act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)) w
  have h := tripleIndependentCell_assoc R L NR NL A B D xs ys ws p q r P Q hl hr
  rw [independentAssocLeftAug_flat, independentAssocRightAug_flat, independentUnit_associative R J P U]
  change HEq (s ≫ P.assoc I I I ≫ independentUnitMergeRight R J)
    (α ≫ t ≫ independentUnitMergeRight R J)
  rw [← Category.assoc s, ← Category.assoc α]
  exact structural_seq_heq (K:=coeff (C:=C)) e rfl rfl h HEq.rfl


set_option backward.isDefEq.respectTransparency false in
theorem independentAssocLeft_repr :
    independentAug R L (J.ρ I) (independentAug R L (J.ρ I) (wordAug A xs p) (wordAug B ys q)) (wordAug D ws r) =
      wordAug (crossLabel T (crossLabel T A B) D) ((xs.product ys).product ws)
        (independentAssocLeftAug R L J A B D xs ys ws p q r) := by
  rw [independentAug_ordered_eq, independentAug_ordered_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem independentAssocRight_repr :
    independentAug R L (J.ρ I) (wordAug A xs p) (independentAug R L (J.ρ I) (wordAug B ys q) (wordAug D ws r)) =
      wordAug (crossLabel T A (crossLabel T B D)) (xs.product (ys.product ws))
        (independentAssocRightAug R L J A B D xs ys ws p q r) := by
  rw [independentAug_ordered_eq, independentAug_ordered_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
noncomputable def independentAssocIso
    [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c)
    (ι : ∀ a b d, IsIso (P.assoc a b d)) (hn : (xs.product (ys.product ws)).Nodup) :
    NativeAugmentedIso
      (independentAug R L (J.ρ I) (independentAug R L (J.ρ I) (wordAug A xs p) (wordAug B ys q)) (wordAug D ws r))
      (independentAug R L (J.ρ I) (wordAug A xs p) (independentAug R L (J.ρ I) (wordAug B ys q) (wordAug D ws r))) := by
  let H := crossLabel T (crossLabel T A B) D
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let G := H ∘ g.symm
  let K := crossLabel T A (crossLabel T B D)
  let v := (xs.product ys).product ws
  let w := xs.product (ys.product ws)
  let s := independentAssocLeftAug R L J A B D xs ys ws p q r
  let t := independentAssocRightAug R L J A B D xs ys ws p q r
  have hread : v.map g = w := tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)
  let e := (std_fold_map G g v).symm.trans (congrArg (fold 𝒮 Zₐ G) hread)
  let φ (z : X × Y × W) : G z ≅ K z := by
    let _ := ι (A z.1) (B z.2.1) (D z.2.2)
    exact asIso (P.assoc (A z.1) (B z.2.1) (D z.2.2))
  let s' := eqToHom e.symm ≫ s
  have hp : AddressOrder.mapSum additiveStructure G (.ident w) ≫
      act 𝒮 Zₐ (fun z => (φ z).hom) w ≫ t = s' := by
    change 𝟙 _ ≫ act 𝒮 Zₐ (fun z => (φ z).hom) w ≫ t = _
    rw [Category.id_comp]
    exact eq_of_heq ((independentAssocAug_heq R L J P NR NL Q U A B D xs ys ws p q r hl hr).symm.trans
      (hom_source_pin_heq e.symm s).symm)
  have hs : wordAug H v s = wordAug G w s' :=
    wordAug_read_eq G g v w hread _ _ (hom_source_pin_heq e.symm s).symm
  exact (wordAugIso G K (.ident w) hn φ s' t hp).retarget
    ((independentAssocLeft_repr R L J A B D xs ys ws p q r).trans hs).symm
    (independentAssocRight_repr R L J A B D xs ys ws p q r).symm

set_option backward.isDefEq.respectTransparency false in
theorem independentAssocIso_pointwise_heq
    [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c)
    (ι : ∀ a b d, IsIso (P.assoc a b d)) (hn : (xs.product (ys.product ws)).Nodup) :
    HEq (independentAssocIso R L J P NR NL Q U A B D xs ys ws p q r hl hr ι hn).hom.native
      (wordPointwise (xs.product (ys.product ws)) (fun z => P.assoc (A z.1) (B z.2.1) (D z.2.2))) := by
  unfold independentAssocIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (wordAugIso_ident_pointwise _ _ _ _ _ _))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
