module
public import ContextualComposition.NativeWordChartSpan

@[expose] public section
/-! Transport the selected block augmentation to the literal restriction
of the original whole native dependent morphism. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X U X' U' : Type u} [DecidableEq X'] [DecidableEq U']
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
variable {T : Bi (coeff (C:=C))}


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
/-- The actual global native dependent map restricted along the chosen
parent selector preserves the selected block augmentations, with precisely
the source and target addresses identified by their exact reading maps. -/
theorem restrictedDependent_block_preserves
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    {I : C} (J : UnitCompat R I)
    {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (hp : D.Preserves hn hk δ δ' ε ε')
    (h : (dependentWord xs' us').Nodup) (hn₀ : (dependentWord xs us).Nodup)
    (j : Fin xs'.length) (hh : (us' xs'[j]).Nodup)
    (hx : ∀ x : D.Slice xs'[j], (us x.val).Nodup)
    (hw : (selectedBlockWord D xs'[j]).Nodup)
    [∀ x : D.Slice xs'[j], (leftFactor T (V x.val)).LaxBraided]
    (hl : ∀ x : D.Slice xs'[j], SameLeftGather T (V x.val) L) :
    let P := origDependentWordMap D R L h
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    let x := fibreList (sel ∘ P.addr) j
    let y := fibreList sel j
    let A := dependentLabels (T:=T) V W
    let B := dependentLabels (T:=T) V' W'
    let A₀ := (wordFamily A (dependentWord xs us)).val
    let B₀ := (wordFamily B (dependentWord xs' us')).val
    let B₁ := fun t => T.obj (V' a) (W' a t)
    let wx := selectedBlockWord D a
    let wy := us' a
    let f := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
    let g := dependentSliceRelabel D a
    let ex := origDependent_block_source_word D h hn R L j
    let ey := origDependent_block_target_length (us':=us') hn j
    let q : ∀ i : Fin y.length, B₀ y[i] = B₁ wy[Fin.cast ey i] :=
      fun i => congrArg B (origDependent_block_target_read (us':=us') hn j i)
    let e := ((std_fold_map A f x).symm.trans (congrArg (fold 𝒮 Zₐ A) ex)).trans (std_fold_map A g wx)
    let o := finiteOutputPin ey (fun i : Fin y.length => B₀ y[i]) (fun i : Fin wy.length => B₁ wy[i]) q
    let α := selectedParentSourceAugCell D a R L J (List.getElem_mem _) δ
    let β := selectedParentTargetAugCell (us':=us') (W':=W') (V':=V') a R L J (δ' a)
    (fibreRestrictNative P sel j).comp
        (wordAug B₀ y (eqToHom (wordTotalPin B₀ y).symm ≫ eqToHom o ≫ eqToHom (wordTotalPin B₁ wy) ≫ β)).ε =
      (wordAug A₀ x (eqToHom e ≫ α)).ε := by
  intro P sel a x y A B A₀ B₀ B₁ wx wy f g ex ey q e o α β
  let r := wordNativePartitionOrder P.addr (fibreRestrict_support P.addr sel j) (fibreList_nodup sel j)
  let r' := wordNativePartitionOrder (selectedChildAddr D a) (selectedChild_support D a) hh
  let y₀ := fun i : Fin y.length => y[i]
  let y₁ := fun i : Fin wy.length => wy[i]
  let p' := fun i : Fin wy.length => selectedChildBlockCell D R L a (List.getElem_mem _) (y₁ i) (List.getElem_mem _)
  let p := fun i : Fin y.length =>
    eqToHom (congrArg (fold 𝒮 Zₐ A₀) (restricted_fibre P.addr sel j (List.getElem_mem (l:=y) (n:=i.val) i.isLt))) ≫ P.cell (y₀ i)
  let b := eqToHom (wordTotalPin B₀ y).symm ≫ eqToHom o ≫ eqToHom (wordTotalPin B₁ wy) ≫ β
  change (wordNativeMap P.addr (fibreRestrict_support P.addr sel j) (fibreList_nodup sel j) A₀ B₀ p).comp
    (wordAug B₀ y b).ε = (wordAug A₀ x (eqToHom e ≫ α)).ε
  apply (wordNativeMap_preserving_iff P.addr (fibreRestrict_support P.addr sel j)
    (fibreList_nodup (sel ∘ P.addr) j) (fibreList_nodup sel j) A₀ B₀ p r (eqToHom e ≫ α) b).mpr
  let G := fun i : Fin y.length => wordFibre x P.addr (y₀ i)
  let H := fun i : Fin wy.length => wordFibre wx (selectedChildAddr D a) (y₁ i)
  let w := List.finRange y.length
  let w' := List.finRange wy.length
  let eL := fun i => restrictedDependent_fibre_read D h hn R L j i
  have hb : (x.map f).Nodup := by
    have hF := wordCarrier_block_fibre (origDepCarrier D) Prod.fst (origDepCarrier_support D)
      (outerBlock_support (us':=us')) h hn j
    change x.map f = wordFibre (dependentWord xs us) (D.parent ∘ Prod.fst) a at hF
    rw [hF]
    exact hn₀.filter _
  have hf (i : Fin y.length) : p i =
      eqToHom (((std_fold_map A f (G i)).symm.trans (congrArg (fold 𝒮 Zₐ A) (eL i))).trans
        (std_fold_map A g (H (Fin.cast ey i)))) ≫ p' (Fin.cast ey i) ≫ eqToHom (q i).symm :=
    restrictedDependent_cell_read D h hn R L j i
  have s := finiteWordChart_span A f g x wx ey G H (B₀ ∘ y₀) (B₁ ∘ y₁) eL q ex hb r r' p'
  dsimp only at s
  have ha : (selectedChildBlockMap D R L a (List.getElem_mem _) hh).comp (wordAug B₁ wy β).ε =
      (wordAug (A ∘ g) wx α).ε :=
    (selectedParentBlockAugMap D a R L N NL J hp (List.getElem_mem _) hh hx hw hl).preserves
  have z := (wordNativeMap_preserving_iff (selectedChildAddr D a) (selectedChild_support D a) hw hh
    (A ∘ g) B₁ p' r' α β).mp ha
  let k := eqToHom (wordTotalPin B₀ y)
  have d : k ≫ b = eqToHom o ≫ eqToHom (wordTotalPin B₁ wy) ≫ β := by
    change eqToHom (wordTotalPin B₀ y) ≫ eqToHom (wordTotalPin B₀ y).symm ≫ _ = _
    have h₀ : eqToHom (wordTotalPin B₀ y) ≫ eqToHom (wordTotalPin B₀ y).symm = 𝟙 _ := by
      rw [eqToHom_trans]
      rfl
    rw [reassoc_of% h₀]
  change AddressOrder.mapSum additiveStructure A₀ r ≫ rowsChart A₀ G w ≫ act 𝒮 Zₐ p w ≫ (k ≫ b) =
     eqToHom e ≫ α
  rw [d]
  let u := fun i : Fin y.length =>
    eqToHom (((std_fold_map A f (G i)).symm.trans (congrArg (fold 𝒮 Zₐ A) (eL i))).trans
      (std_fold_map A g (H (Fin.cast ey i)))) ≫ p' (Fin.cast ey i) ≫ eqToHom (q i).symm
  have h₀ : act 𝒮 Zₐ p w = act 𝒮 Zₐ u w := congrArg (fun h => act 𝒮 Zₐ h w) (funext hf)
  rw [h₀]
  have S := congrArg (fun h => h ≫ eqToHom (wordTotalPin B₁ wy) ≫ β) s
  simp only [Category.assoc] at S
  refine S.trans ?_
  exact congrArg (fun u => eqToHom e ≫ u) z

omit [DecidableEq U'] in
set_option backward.isDefEq.respectTransparency false in
theorem restrictedDependent_target_cell
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I) (hn : xs'.Nodup) (j : Fin xs'.length) :
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    let y := fibreList sel j
    let B := dependentLabels (T:=T) V' W'
    let B₀ := (wordFamily B (dependentWord xs' us')).val
    let B₁ := fun t => T.obj (V' a) (W' a t)
    let wy := us' a
    let ey := origDependent_block_target_length (us':=us') hn j
    let q : ∀ i : Fin y.length, B₀ y[i] = B₁ wy[Fin.cast ey i] :=
      fun i => congrArg B (origDependent_block_target_read (us':=us') hn j i)
    let o := finiteOutputPin ey (fun i : Fin y.length => B₀ y[i]) (fun i : Fin wy.length => B₁ wy[i]) q
    (nativeDependentRowCollapse R L J xs' us' V' W' δ hn).cell j =
      eqToHom (wordTotalPin B₀ y).symm ≫ eqToHom o ≫ eqToHom (wordTotalPin B₁ wy) ≫
        selectedParentTargetAugCell (us':=us') (W':=W') (V':=V') a R L J (δ a) := by
  intro s a y B B₀ B₁ wy ey q o
  let c := (wordCarrier_fibre_pin Prod.fst (outerBlock_support (us':=us')) hn B j)
  let e := congrArg (fold 𝒮 Zₐ B) (targetParentBlockWord (us':=us') hn (List.getElem_mem (l:=xs') (n:=j.val) j.isLt))
  let p := std_fold_map B (fun t => (a,t)) wy
  let E := (Lin.left L (V' a)).collect (W' a) wy ≫ T.map (𝟙 (V' a)) (δ a) ≫ J.ρ (V' a)
  rw [selectedParentTargetAug_raw]
  change eqToHom c ≫ eqToHom e ≫ eqToHom p ≫ E =
    eqToHom (wordTotalPin B₀ y).symm ≫ eqToHom o ≫ eqToHom (wordTotalPin B₁ wy) ≫ E
  rw [reassoc_of% eqToHom_trans c e, reassoc_of% eqToHom_trans (c.trans e) p,
    reassoc_of% eqToHom_trans (wordTotalPin B₀ y).symm o,
    reassoc_of% eqToHom_trans ((wordTotalPin B₀ y).symm.trans o) (wordTotalPin B₁ wy)]

set_option backward.isDefEq.respectTransparency false in
theorem origDependent_parent_carrier [DecidableEq X]
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (hn₀ : xs.Nodup) (hn : xs'.Nodup) (hh : (dependentWord xs' us').Nodup) :
    let p := origDependentWordMap D R L hh
    let s := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let q := nativeDependentRowCollapse R L J xs us V W δ hn₀
    let o := D.outerNative hn
    s ∘ p.addr = o.addr ∘ q.addr := by
  intro p s q o
  ext i
  apply hn.getElem_inj.mp
  change xs'[s (p.addr i)] = xs'[o.addr (q.addr i)]
  change xs'[wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
      (wordCarrier (origDepCarrier D) (origDepCarrier_support D) hh i)] =
    xs'[wordCarrier D.parent D.parent_mem hn (wordCarrier Prod.fst (outerBlock_support (us':=us)) hn₀ i)]
  rw [wordCarrier_get, wordCarrier_get, wordCarrier_get, wordCarrier_get]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The selected-parent merge read on the exact carrier fibre of the
original native dependent arrow. -/
noncomputable def selectedParentNativeMerge (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (hn : xs'.Nodup) (ht : (dependentWord xs' us').Nodup) (j : Fin xs'.length) :
    let p := origDependentWordMap D R L ht
    let s := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    standardPushObj (s ∘ p.addr) (wordFamily (dependentLabels (T:=T) V W) (dependentWord xs us)).val j ⟶ V' xs'[j] :=
  let p := origDependentWordMap D R L ht
  let s := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
  let A := dependentLabels (T:=T) V W
  let x := fibreList (s ∘ p.addr) j
  let f := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
  let a := xs'[j]
  let g := dependentSliceRelabel D a
  let e := origDependent_block_source_word D ht hn R L j
  eqToHom (((std_fold_map A f x).symm.trans (congrArg (fold 𝒮 Zₐ A) e)).trans (std_fold_map A g (selectedBlockWord D a))) ≫
    selectedParentSourceAugCell D a R L J (List.getElem_mem _) δ

set_option backward.isDefEq.respectTransparency false in
theorem origDependent_then_targetCollapse
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    {I : C} (J : UnitCompat R I)
    {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (hp : D.Preserves hn hk δ δ' ε ε')
    (h : (dependentWord xs' us').Nodup) (hn₀ : (dependentWord xs us).Nodup)
    (hc : ∀ j : Fin xs'.length, (us' xs'[j]).Nodup)
    (hx : ∀ j : Fin xs'.length, ∀ x : D.Slice xs'[j], (us x.val).Nodup)
    (hw : ∀ j : Fin xs'.length, (selectedBlockWord D xs'[j]).Nodup)
    [∀ x : X, (leftFactor T (V x)).LaxBraided]
    (hl : ∀ x : X, SameLeftGather T (V x) L) :
    let P := origDependentWordMap D R L h
    let Q := nativeDependentRowCollapse R L J xs' us' V' W' δ' hn
    P.comp Q = Hom.mk (S:=ℙ) (A:=wordFamily (dependentLabels (T:=T) V W) (dependentWord xs us))
      (B:=wordFamily V' xs') (Q.addr ∘ P.addr) (selectedParentNativeMerge D R L J δ hn h) := by
  intro P Q
  apply paste_native_blocks
  intro j
  have b := restrictedDependent_block_preserves D R L N NL J hp h hn₀ j (hc j) (hx j) (hw j) (fun x => hl x.val)
  have g := restrictedDependent_target_cell (us':=us') (V':=V') (W':=W') R L J δ' hn j
  dsimp only at b g
  have c := congrArg (fun a => (fibreRestrictNative P Q.addr j).comp
    (wordAug (wordFamily (dependentLabels (T:=T) V' W') (dependentWord xs' us')).val (fibreList Q.addr j) a).ε) g
  exact c.trans b

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
