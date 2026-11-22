module
public import ContextualComposition.NativeDependentBlockPaste

@[expose] public section
/-! The original dependent native arrow commutes with the two native
parent-projection collapses, before the one final outer augmentation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush
local notation "𝒮" => binary (Additive.sum Additive.ofBraided)
local notation "Zₐ" => 𝟙_ _
variable {X U X' U' : Type u} [DecidableEq X] [DecidableEq X'] [DecidableEq U']
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
variable {T : Bi (coeff (C:=C))}

theorem sourceCollapse_outer_fibre
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (hn₀ : xs.Nodup) (hn : xs'.Nodup) (j : Fin xs'.length) :
    let q := nativeDependentRowCollapse R L J xs us V W δ hn₀
    let o := D.outerNative hn
    (fibreList (o.addr ∘ q.addr) j).map (fun i => (dependentWord xs us)[i]) =
      dependentWord (parentFibreA xs D.parent xs'[j]) us :=
  (wordCarrier_block_fibre Prod.fst D.parent (outerBlock_support (us':=us)) D.parent_mem hn₀ hn j).trans
    (wordFibre_parent D.parent xs us xs'[j])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem sourceCollapse_outer_rawCell
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (hn₀ : xs.Nodup) (hn : xs'.Nodup) (hw : (dependentWord xs us).Nodup) (j : Fin xs'.length) :
    let q := nativeDependentRowCollapse R L J xs us V W δ hn₀
    let o := D.outerNative hn
    let A := dependentLabels (T:=T) V W
    let g := fun i : Fin (dependentWord xs us).length => (dependentWord xs us)[i]
    let s := fibreList (o.addr ∘ q.addr) j
    let h := sourceCollapse_outer_fibre D R L J δ hn₀ hn j
    let PF := parentFibreA xs D.parent xs'[j]
    (q.comp o).cell j =
      eqToHom ((std_fold_map A g s).symm.trans (congrArg (fold 𝒮 Zₐ A) h)) ≫
        rowsChart A (fun x => (us x).map (fun u => (x,u))) PF ≫
        act 𝒮 Zₐ (rawDependentRowAug R L J us V W δ) PF ≫ D.outer xs'[j] (List.getElem_mem _) := by
  intro q o A g s hs PF
  let A₀ := (wordFamily A (dependentWord xs us)).val
  let b := fibreList o.addr j
  let y := fun k : Fin xs.length => xs[k]
  let f := fun x : X => (us x).map (fun u => (x,u))
  let F := fold 𝒮 Zₐ A
  let L₀ := fibreList q.addr
  let L₁ := f ∘ y
  let r := splitOrder q.addr o.addr j
  let p := rawDependentRowAug R L J us V W δ
  let p' := fun k : Fin xs.length => p (y k)
  have m (k : Fin xs.length) : (L₀ k).map g = L₁ k :=
    (wordCarrier_fibre Prod.fst (outerBlock_support (us':=us)) hn₀ k).trans
      (targetParentBlockWord (us':=us) hn₀ (List.getElem_mem _))
  let e := fun k => (std_fold_map A g (L₀ k)).symm.trans (congrArg F (m k))
  have he (k : Fin xs.length) : q.cell k = eqToHom (e k) ≫ p' k := by
    change eqToHom (wordCarrier_fibre_pin Prod.fst (outerBlock_support (us':=us)) hn₀ A k) ≫
      (eqToHom (congrArg F (targetParentBlockWord (us':=us) hn₀ (List.getElem_mem (l:=xs) (n:=k.val) k.isLt))) ≫ p' k) =
        eqToHom (e k) ≫ p' k
    rw [← Category.assoc, eqToHom_trans]
  have h₀ := wordChart_retag A (V ∘ y) g s L₀ L₁ b m r p'
  dsimp only at h₀
  let a := (std_fold_map A g s).symm
  let ds : (b.flatMap L₀).map g = b.flatMap L₁ :=
    (List.map_flatMap (f:=g) (g:=L₀) (l:=b)).trans
      (congrArg (fun k => b.flatMap k) (funext m))
  let q' := (r.relabel g).seq (castOrder ds)
  let ht : b.map y = PF := wordCarrier_fibre D.parent D.parent_mem hn j
  let k := (std_fold_map V y b).symm.trans (congrArg (fold 𝒮 Zₐ V) ht)
  let d : b.flatMap L₁ = PF.flatMap f :=
    (List.flatMap_map y f b).symm.trans (congrArg (fun v => v.flatMap f) ht)
  have h₁ : rowsChart A L₁ b ≫ act 𝒮 Zₐ p' b ≫ eqToHom k =
      eqToHom (congrArg F d) ≫ rowsChart A f PF ≫ act 𝒮 Zₐ p PF :=
    rowsChart_index_apply A f y p b ht
  have h₂ : AddressOrder.mapSum additiveStructure A q' ≫ eqToHom (congrArg F d) = eqToHom (congrArg F hs) := by
    let h : (s.map g).Nodup := hs ▸ (by
      rw [← wordFibre_parent D.parent xs us xs'[j]]
      exact hw.filter _)
    have z := tagged_permutation_coherent A h (q'.seq (castOrder d)) (castOrder hs)
    change AddressOrder.mapSum additiveStructure A q' ≫ AddressOrder.mapSum additiveStructure A (castOrder d) =
      AddressOrder.mapSum additiveStructure A (castOrder hs) at z
    rw [castOrder_map, castOrder_map] at z
    exact z
  let β := D.outer xs'[j] (List.getElem_mem _)
  have hq : o.cell j = eqToHom k ≫ β := rfl
  have eq : q.cell = fun k => eqToHom (e k) ≫ p' k := funext he
  change (AddressOrder.mapSum additiveStructure A₀ r ≫ rowsChart A₀ L₀ b) ≫ act 𝒮 Zₐ q.cell b ≫ o.cell j =
    eqToHom (a.trans (congrArg F hs)) ≫ rowsChart A f PF ≫ act 𝒮 Zₐ p PF ≫ β
  rw [hq,eq]
  simp only [Category.assoc]
  have s₀ := congrArg (fun u => u ≫ eqToHom k ≫ β) h₀
  simp only [Category.assoc] at s₀
  refine s₀.trans ?_
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% eqToHom_trans a (congrArg F hs)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
omit [DecidableEq X] in
theorem selectedParentNativeMerge_raw
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (hn : xs'.Nodup) (ht : (dependentWord xs' us').Nodup) (j : Fin xs'.length) :
    let mt := origDependentWordMap D R L ht
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let A := dependentLabels (T:=T) V W
    let g := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
    let x := fibreList (sel ∘ mt.addr) j
    let PF := parentFibreA xs D.parent xs'[j]
    let h : x.map g = dependentWord PF us :=
      (origDependent_block_source_word D ht hn R L j).trans ((selectedBlockWord_map D xs'[j]).trans
        (wordFibre_parent D.parent xs us xs'[j]))
    selectedParentNativeMerge D R L J δ hn ht j =
      eqToHom ((std_fold_map A g x).symm.trans (congrArg (fold 𝒮 Zₐ A) h)) ≫
        rowsChart A (fun y => (us y).map (fun u => (y,u))) PF ≫
        act 𝒮 Zₐ (rawDependentRowAug R L J us V W δ) PF ≫ D.outer xs'[j] (List.getElem_mem _) := by
  intro mt sel A g x PF h
  let a := xs'[j]
  let s := D.slice a
  let Q := selectedBlockWord D a
  let F := fold 𝒮 Zₐ A
  let f := dependentSliceRelabel D a
  let y := fun x : D.Slice a => x.val
  let B := A ∘ f
  let R₁ := fun x : X => (us x).map (fun u => (x,u))
  let R₀ := fun x : D.Slice a => (us x.val).map (fun u => (x,u))
  let Z := R₁ ∘ y
  let p := rawDependentRowAug R L J us V W δ
  let q := fun x : D.Slice a => (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫
    T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val)
  let e := fun x : D.Slice a => eqToHom (std_fold_map B (fun t => (x,t)) (us x.val))
  have h₀ (a : D.Slice a) : (R₀ a).map f = Z a := by
    unfold R₀ Z R₁ y f dependentSliceRelabel
    rw [List.map_map]
    rfl
  let v := fun a => eqToHom ((std_fold_map A f (R₀ a)).symm.trans (congrArg F (h₀ a)))
  have hv (a : D.Slice a) : e a ≫ q a = v a ≫ p (y a) := by
    let x := (std_fold_map A f (R₀ a)).symm.trans (congrArg F (h₀ a))
    let z := std_fold_map A (fun t => (y a,t)) (us a.val)
    change e a ≫ q a = eqToHom x ≫ eqToHom z ≫ q a
    rw [reassoc_of% eqToHom_trans x z]
  have ha : act 𝒮 Zₐ e s ≫ act 𝒮 Zₐ q s = act 𝒮 Zₐ v s ≫ act 𝒮 Zₐ (fun a => p (y a)) s :=
    (act_seq 𝒮 Zₐ e q s).trans ((congrArg (fun k => act 𝒮 Zₐ k s) (funext hv)).trans (act_seq 𝒮 Zₐ v _ s).symm)
  let d : Q.map f = s.flatMap Z :=
    (List.map_flatMap (f:=f) (g:=R₀) (l:=s)).trans
      (congrArg (fun k => s.flatMap k) (funext h₀))
  let E := (std_fold_map A f Q).symm.trans (congrArg F d)
  have hc : rowsChart B R₀ s ≫ act 𝒮 Zₐ v s = eqToHom E ≫ rowsChart A Z s :=
    rowsChart_relabel_input_inv A f R₀ h₀ s
  let h₁ : s.map y = PF := sliceWord_map xs D.parent a
  let u := (std_fold_map V y s).symm.trans (congrArg (fold 𝒮 Zₐ V) h₁)
  let w : s.flatMap Z = PF.flatMap R₁ :=
    (List.flatMap_map y R₁ s).symm.trans (congrArg (fun k => k.flatMap R₁) h₁)
  have h₂ : rowsChart A Z s ≫ act 𝒮 Zₐ (fun a => p (y a)) s ≫ eqToHom u =
      eqToHom (congrArg F w) ≫ rowsChart A R₁ PF ≫ act 𝒮 Zₐ p PF :=
    rowsChart_index_apply A R₁ y p s h₁
  let z₀ := ((std_fold_map A g x).symm.trans (congrArg F (origDependent_block_source_word D ht hn R L j))).trans (std_fold_map A f Q)
  let z := (std_fold_map A g x).symm.trans (congrArg F h)
  let β := D.outer a (List.getElem_mem _)
  change eqToHom z₀ ≫ (rowsChart B R₀ s ≫ act 𝒮 Zₐ e s) ≫ act 𝒮 Zₐ q s ≫ (eqToHom u ≫ β) =
    eqToHom z ≫ rowsChart A R₁ PF ≫ act 𝒮 Zₐ p PF ≫ β
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hc, reassoc_of% h₂, reassoc_of% eqToHom_trans z₀ E,
    reassoc_of% eqToHom_trans (z₀.trans E) (congrArg F w)]

section Global
variable (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable {I : C} (J : UnitCompat R I)
variable {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
variable {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
variable {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
variable {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
variable (hp : D.Preserves hn hk δ δ' ε ε')
variable (h : (dependentWord xs' us').Nodup) (hn₀ : (dependentWord xs us).Nodup) (ho : xs.Nodup)
variable (hc : ∀ j : Fin xs'.length, (us' xs'[j]).Nodup)
variable (hx : ∀ j : Fin xs'.length, ∀ x : D.Slice xs'[j], (us x.val).Nodup)
variable (hw : ∀ j : Fin xs'.length, (selectedBlockWord D xs'[j]).Nodup)
variable [∀ x : X, (leftFactor T (V x)).LaxBraided]
variable (hl : ∀ x : X, SameLeftGather T (V x) L)

include N NL hp hn₀ hc hx hw hl in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
/-- The literal native dependent word map commutes with the two actual
parent collapses. This assertion is before, and stronger than, merely
preserving one postcomposed terminal augmentation. -/
theorem origDependent_parent_square :
    (origDependentWordMap D R L h).comp (nativeDependentRowCollapse R L J xs' us' V' W' δ' hn) =
      (nativeDependentRowCollapse R L J xs us V W δ ho).comp (D.outerNative hn) := by
  let A := dependentLabels (T:=T) V W
  let A₀ := (wordFamily A (dependentWord xs us)).val
  let F := fold 𝒮 Zₐ A
  let P := origDependentWordMap D R L h
  let Q := nativeDependentRowCollapse R L J xs' us' V' W' δ' hn
  let U := nativeDependentRowCollapse R L J xs us V W δ ho
  let O := D.outerNative hn
  have e : Q.addr ∘ P.addr = O.addr ∘ U.addr := origDependent_parent_carrier D R L J δ ho hn h
  have z := origDependent_then_targetCollapse D R L N NL J hp h hn₀ hc hx hw hl
  dsimp only at z
  rw [z]
  apply (native_hom_iff_cell e _ _).mpr
  intro j
  have p := selectedParentNativeMerge_raw D R L J δ hn h j
  have q := sourceCollapse_outer_rawCell D R L J δ ho hn hn₀ j
  dsimp only at p q
  let a := xs'[j]
  let g := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
  let x := fibreList (Q.addr ∘ P.addr) j
  let y := fibreList (O.addr ∘ U.addr) j
  let PF := parentFibreA xs D.parent a
  let rows := fun t : X => (us t).map (fun u => (t,u))
  let c := rowsChart A rows PF ≫ act 𝒮 Zₐ (rawDependentRowAug R L J us V W δ) PF ≫ D.outer a (List.getElem_mem _)
  let ex := (origDependent_block_source_word D h hn R L j).trans
    ((selectedBlockWord_map D a).trans (wordFibre_parent D.parent xs us a))
  let ey := sourceCollapse_outer_fibre D R L J δ ho hn j
  let k := congrArg (fun a => standardPushObj a A₀ j) e
  let l := (std_fold_map A g x).symm.trans (congrArg F ex)
  let m := (std_fold_map A g y).symm.trans (congrArg F ey)
  change selectedParentNativeMerge D R L J δ hn h j = eqToHom k ≫ (U.comp O).cell j
  rw [p]
  have q' := congrArg (fun k' => eqToHom k ≫ k') q
  refine Eq.trans ?_ q'.symm
  change eqToHom l ≫ c = eqToHom k ≫ eqToHom m ≫ c
  rw [reassoc_of% eqToHom_trans k m]

set_option backward.isDefEq.respectTransparency false in
include N NL hp hn₀ ho hc hx hw hl in
/-- Literal unary dependent operation on the actual ordered augmented
input data, with independent continuation carrier changes and noninjective
parent carrier changes. The native arrow is not chosen by the proof. -/
noncomputable def origDependentWordAugMap :
    AugHom ℙ
      (dependentWordAug R L J xs us V W (fun x => eqToHom (std_fold_map id (W x) (us x)) ≫ δ x) ε)
      (dependentWordAug R L J xs' us' V' W' (fun x => eqToHom (std_fold_map id (W' x) (us' x)) ≫ δ' x) ε') where
  native := origDependentWordMap D R L h
  preserves := by
    let P := origDependentWordMap D R L h
    let Q := nativeDependentRowCollapse R L J xs' us' V' W' δ' hn
    let U := nativeDependentRowCollapse R L J xs us V W δ ho
    let O := D.outerNative hn
    let e := (wordAug V' xs' ε').ε
    let d := (wordAug V xs ε).ε
    have h₁ := nativeDependentRowCollapse_preserves R L J xs' us' V' W' δ' hn h ε'
    have h₂ := nativeDependentRowCollapse_preserves R L J xs us V W δ ho hn₀ ε
    have hp₀ : O.comp e = d := hp.outer
    have sq : P.comp Q = U.comp O := origDependent_parent_square D R L N NL J hp h hn₀ ho hc hx hw hl
    change P.comp (dependentWordAug R L J xs' us' V' W'
        (fun x => eqToHom (std_fold_map id (W' x) (us' x)) ≫ δ' x) ε').ε =
      (dependentWordAug R L J xs us V W (fun x => eqToHom (std_fold_map id (W x) (us x)) ≫ δ x) ε).ε
    rw [← h₁, ← Hom.comp_assoc, sq]
    exact (Hom.comp_assoc U O e).trans ((congrArg (fun x => U.comp x) hp₀).trans h₂)

end Global

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
