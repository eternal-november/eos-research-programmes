module
public import ContextualComposition.NativeDependentDirectAssembly
@[expose] public section

/-! Native ordered rectangles: identity and composition use unchanged
independent whole-fibre cells. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}

set_option backward.isDefEq.respectTransparency false in
theorem independent_one_pair_unit
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type w} (A : X → C) (B : Y → C) (x : X) (y : Y)
    [(leftFactor T (A x)).LaxBraided] [(rightFactor (T:=T) (B y)).LaxBraided]
    (_hl : SameLeftGather T (A x) L) (_hr : SameRightGather R (B y)) :
    let G := fun p : X × Y => T.obj (A p.1) (B p.2)
    rectWordChart G [x] [y] ≫ rowGather R L A B [x] [y] ≫ T.map (ρ_ (A x)).hom (ρ_ (B y)).hom =
      (ρ_ (T.obj (A x) (B y))).hom := by
  intro G
  let a := A x
  let b := B y
  let h := T.obj a b
  let c := T.obj a (b ⊗ Zₐ)
  let q := fun i => T.map (𝟙 (A i)) (ρ_ b).hom
  let p := fun i => (Lin.left L (A i)).collect B [y]
  have q' := gather_nat R A (ρ_ b).hom [x]
  change DependentFibre.gather R A (b ⊗ Zₐ) [x] ≫ T.map (𝟙 (a ⊗ Zₐ)) (ρ_ b).hom =
    act 𝒮 Zₐ q [x] ≫ DependentFibre.gather R A b [x] at q'
  have h0 : T.map (𝟙 (a ⊗ Zₐ)) (ρ_ b).hom ≫ T.map (ρ_ a).hom (𝟙 b) = T.map (ρ_ a).hom (ρ_ b).hom := by
    have z := bi_map_comp (T:=T) (𝟙 (a ⊗ Zₐ)) (ρ_ a).hom (ρ_ b).hom (𝟙 b)
    rw [Category.id_comp, Category.comp_id] at z
    exact z
  have h1 : rectWordChart G [x] [y] = (ρ_ (h ⊗ Zₐ)).inv := by
    have H := rectPairExpr_chart G [x] [y]
    change compressGrid G (.bin (.bin (.leaf (x,y)) .zero) .zero) ≫ 𝟙 _ =
      𝟙 _ ≫ rectWordChart G [x] [y] at H
    rw [Category.id_comp, Category.comp_id] at H
    have j : compressGrid G (.bin (.bin (.leaf (x,y)) .zero) .zero) = (ρ_ (h ⊗ Zₐ)).inv := by
      change join additiveStructure G [(x,y)] [] ≫ (compressGrid G (.bin (.leaf (x,y)) .zero) ⊗ₘ 𝟙 Zₐ) = _
      have e : compressGrid G (.bin (.leaf (x,y)) .zero) = 𝟙 (h ⊗ Zₐ) := by
        have j := compressGrid_leafWord G (fun t : Y => (x,t)) [y]
        change _ ≫ 𝟙 _ = 𝟙 _ at j
        rw [Category.comp_id] at j
        exact j
      rw [e]
      let J : (h ⊗ Zₐ) ⟶ (h ⊗ Zₐ) ⊗ Zₐ := join additiveStructure G [(x,y)] []
      change J ≫ (𝟙 (h ⊗ Zₐ) ⊗ₘ 𝟙 Zₐ) = _
      rw [tensorHom_id, id_whiskerRight, Category.comp_id]
      have j := std_join_right_unit G [(x,y)]
      change 𝟙 _ ≫ J = _ at j
      rw [Category.id_comp] at j
      exact j
    exact H.symm.trans j
  have h2 : p x ≫ q x = (ρ_ h).hom := by
    have d := collect_singleton (leftFactor T a) B y
    unfold a at d
    rw [leftFactor_sameCollect T (A x) L _hl] at d
    exact d
  have h3 : DependentFibre.gather R A b [x] ≫ T.map (ρ_ a).hom (𝟙 b) = (ρ_ h).hom := by
    have d := collect_singleton (rightFactor (T:=T) b) A x
    rw [rightFactor_sameCollect R _hr] at d
    exact d
  have ha : act 𝒮 Zₐ p [x] ≫ act 𝒮 Zₐ q [x] = act 𝒮 Zₐ (fun i => p i ≫ q i) [x] :=
    act_seq (S:=𝒮) (Z:=Zₐ) p q [x]
  change rectWordChart G [x] [y] ≫
    (act 𝒮 Zₐ p [x] ≫ DependentFibre.gather R A (b ⊗ Zₐ) [x]) ≫ T.map (ρ_ a).hom (ρ_ b).hom = _
  rw [h1, ← h0]
  simp only [Category.assoc]
  rw [reassoc_of% q', reassoc_of% ha]
  change (ρ_ (h ⊗ Zₐ)).inv ≫ ((p x ≫ q x) ⊗ₘ 𝟙 Zₐ) ≫
    (DependentFibre.gather R A b [x] ≫ T.map (ρ_ a).hom (𝟙 b)) = _
  rw [h2, h3]
  rw [tensorHom_id, ← rightUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc]


set_option backward.isDefEq.respectTransparency false in
theorem independent_cell_singleton_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type w} (A : X → C) (B : Y → C) (x : X) (y : Y)
    [(leftFactor T (A x)).LaxBraided] [(rightFactor (T:=T) (B y)).LaxBraided]
    (_hl : SameLeftGather T (A x) L) (_hr : SameRightGather R (B y))
    (xs : List X) (ys : List Y) (_ex : xs = [x]) (_ey : ys = [y])
    (p : fold 𝒮 Zₐ A xs ⟶ A x) (q : fold 𝒮 Zₐ B ys ⟶ B y)
    (_hp : HEq p (ρ_ (A x)).hom) (_hq : HEq q (ρ_ (B y)).hom) :
    let G := fun p : X × Y => T.obj (A p.1) (B p.2)
    HEq (rectWordChart G xs ys ≫ independentCell R L A B xs ys p q)
      (ρ_ (T.obj (A x) (B y))).hom := by
  intro G
  subst xs
  subst ys
  have e : p = (ρ_ (A x)).hom := eq_of_heq _hp
  have f : q = (ρ_ (B y)).hom := eq_of_heq _hq
  subst p
  subst q
  unfold independentCell
  exact heq_of_eq (independent_one_pair_unit R L A B x y _hl _hr)

set_option backward.isDefEq.respectTransparency false in
theorem independentNativeWordMap_ident
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (A B : Family C)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    independentNativeWordMap T (Hom.ident (S:=ℙ) A) (Hom.ident (S:=ℙ) B) R L =
      Hom.ident (independentFamily T A B) := by
  unfold independentNativeWordMap
  apply wordNativeMap_ident_of_singleton
  · intro p _
    rcases p with ⟨x,y⟩
    rfl
  · intro i
    let w := independentWord A B
    let t := w[i]
    let x := t.1
    let y := t.2
    let p := Hom.ident (S:=ℙ) A
    let q := Hom.ident (S:=ℙ) B
    let ax := fibreList (id : Fin A.n → Fin A.n) x
    let bx := fibreList (id : Fin B.n → Fin B.n) y
    let _ : (leftFactor T (A.val x)).LaxBraided := lF _
    let _ : (rightFactor (T:=T) (B.val y)).LaxBraided := rF _
    have ep : HEq (p.cell x) (ρ_ (A.val x)).hom := hom_source_pin_heq _ _
    have eq : HEq (q.cell y) (ρ_ (B.val y)).hom := hom_source_pin_heq _ _
    have h := independent_cell_singleton_heq R L A.val B.val x y (_hl _) (_hr _)
      ax bx (fibreList_id x) (fibreList_id y) (p.cell x) (q.cell y) ep eq
    dsimp only at h
    exact (hom_source_pin_heq _ _).trans h


def independentTotalChart (T : Bi (coeff (C:=C))) (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (A B : Family C) : totalFold (independentFamily T A B) ⟶ T.obj (totalFold A) (totalFold B) :=
  eqToHom (wordTotalPin (independentLabels T A B) (independentWord A B)) ≫
    rectWordChart (independentLabels T A B) (List.finRange A.n) (List.finRange B.n) ≫
    rowGather R L A.val B.val (List.finRange A.n) (List.finRange B.n)

set_option backward.isDefEq.respectTransparency false in
theorem independentWholeContinuation_of_sourceChart
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' : Family C} (p : Hom ℙ A A') (q : Hom ℙ B B')
    (r : AddressOrder (Fin A.n × Fin B.n) (independentWord A B)
      ((independentWord A' B').flatMap (wordFibre (independentWord A B) (Prod.map p.addr q.addr))))
    (_S : IndependentProductSourceChart T R L (A:=A) (B:=B) p.addr q.addr r) :
    wholeContinuation (independentNativeWordMap T p q R L) ≫ independentTotalChart T R L A' B' =
      independentTotalChart T R L A B ≫ T.map (wholeContinuation p) (wholeContinuation q) := by
  let a := independentLabels T A B
  let b := independentLabels T A' B'
  let s := independentWord A B
  let t := independentWord A' B'
  let f := Prod.map p.addr q.addr
  let p₀ := independentWordCell T p q R L
  let pin : totalFold (independentFamily T A B) = fold 𝒮 Zₐ a s := wordTotalPin a s
  have H := wholeContinuation_native_raw_target f (independent_word_support p q)
    (independentWord_nodup A B) (independentWord_nodup A' B') a b p₀ r
  unfold independentTotalChart
  simp only [Category.assoc]
  change wholeContinuation (independentNativeWordMap T p q R L) ≫ eqToHom (wordTotalPin b t) ≫ _ = _
  change wholeContinuation (independentNativeWordMap T p q R L) ≫ eqToHom (wordTotalPin b t) = _ at H
  rw [reassoc_of% H]
  have h' := independent_native_terminal_cells T R L NR NL p q
  unfold IndependentProductSourceChart at _S
  dsimp only at _S h'
  rw [h']
  let P := act 𝒮 Zₐ p.cell (List.finRange A'.n)
  let Q := act 𝒮 Zₐ q.cell (List.finRange B'.n)
  let a₀ := AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder p.addr) ≫ rowsChart A.val (fibreList p.addr) (List.finRange A'.n)
  let b₀ := AddressOrder.mapSum additiveStructure B.val (totalPartitionOrder q.addr) ≫ rowsChart B.val (fibreList q.addr) (List.finRange B'.n)
  simp only [Category.assoc]
  rw [reassoc_of% _S, bi_map_comp]
  simp only [wholeContinuation, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem independentWholeContinuation
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' : Family C} (p : Hom ℙ A A') (q : Hom ℙ B B')
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    wholeContinuation (independentNativeWordMap T p q R L) ≫ independentTotalChart T R L A' B' =
      independentTotalChart T R L A B ≫ T.map (wholeContinuation p) (wholeContinuation q) := by
  let f := Prod.map p.addr q.addr
  let w := independentWord A' B'
  let L' := wordFibre (independentWord A B) f
  let g := fun i : Fin w.length => w[i]
  let r := wordNativePartitionOrder f (independent_word_support p q) (independentWord_nodup A' B')
  let d : (List.finRange w.length).flatMap (L' ∘ g) = w.flatMap L' :=
    (List.flatMap_map g L' (List.finRange w.length)).symm.trans
      (congrArg (fun k => k.flatMap L') (finRange_get w))
  let z := r.seq (castOrder d)
  let _ : ∀ x : Fin A.n, (leftFactor T (A.val x)).LaxBraided := fun _ => lF _
  let _ : (rightFactor (T:=T) (fold 𝒮 Zₐ B.val ((List.finRange B'.n).flatMap (fibreList q.addr)))).LaxBraided := rF _
  let _ : (rightFactor (T:=T) (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList q.addr j)) (List.finRange B'.n))).LaxBraided := rF _
  have h := independentProduct_sourceChart T R L N p.addr q.addr z (fun _ => _hl _) (_hr _) (_hr _)
  exact independentWholeContinuation_of_sourceChart R L NR NL p q z h


section RestrictedProduct
theorem restricted_native_fibre_read {A B : Family C} {n : Nat}
    (p : Hom ℙ A B) (g : Fin B.n → Fin n) (j : Fin n) (k : Fin (fibreList g j).length) :
    let as := fibreList (g ∘ p.addr) j
    let bs := fibreList g j
    (fibreList (fibreRestrictNative p g j).addr k).map (fun i : Fin as.length => as[i]) =
      fibreList p.addr bs[k] := by
  intro as bs
  exact (wordCarrier_fibre p.addr (fibreRestrict_support p.addr g j) (fibreList_nodup g j) k).trans
    (restricted_fibre p.addr g j (List.getElem_mem _))

theorem restricted_native_cell_heq {A B : Family C} {n : Nat}
    (p : Hom ℙ A B) (g : Fin B.n → Fin n) (j : Fin n) (k : Fin (fibreList g j).length) :
    HEq ((fibreRestrictNative p g j).cell k) (p.cell (fibreList g j)[k]) := by
  change HEq (eqToHom _ ≫ eqToHom _ ≫ p.cell (fibreList g j)[k]) (p.cell (fibreList g j)[k])
  exact (hom_source_pin_heq _ _).trans (hom_source_pin_heq _ _)

set_option backward.isDefEq.respectTransparency false in
theorem independent_restricted_cell_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {A B A' B' A'' B'' : Family C}
    (p : Hom ℙ A A') (q : Hom ℙ B B') (r : Hom ℙ A' A'') (s : Hom ℙ B' B'')
    (i : Fin A''.n) (j : Fin B''.n)
    (k : Fin (fibreList r.addr i).length × Fin (fibreList s.addr j).length) :
    HEq (independentWordCell T (fibreRestrictNative p r.addr i) (fibreRestrictNative q s.addr j) R L k)
      (independentWordCell T p q R L ((fibreList r.addr i)[k.1],(fibreList s.addr j)[k.2])) := by
  let p₀ := fibreRestrictNative p r.addr i
  let q₀ := fibreRestrictNative q s.addr j
  let ax := fibreList (r.addr ∘ p.addr) i
  let ay := fibreList (s.addr ∘ q.addr) j
  let fx := fun a : Fin ax.length => ax[a]
  let fy := fun a : Fin ay.length => ay[a]
  let v := ((fibreList r.addr i)[k.1],(fibreList s.addr j)[k.2])
  have h := rectangleCell_map_heq' R L A.val B.val fx fy (fibreList p₀.addr k.1) (fibreList q₀.addr k.2)
    (restricted_native_fibre_read p r.addr i k.1) (restricted_native_fibre_read q s.addr j k.2)
    (restricted_native_cell_heq p r.addr i k.1) (restricted_native_cell_heq q s.addr j k.2)
  dsimp only at h
  unfold independentWordCell independentCell
  exact (hom_source_pin_heq _ _).trans (h.trans (hom_source_pin_heq _ _).symm)

end RestrictedProduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem rawPartition_read_span {X X' Y Y' : Type w}
    (A : X → C) (B : Y → C) (B' : Y' → C) (f : X' → X) (g : Y' → Y)
    (src : List X) (src' : List X') (dst : List Y) (dst' : List Y')
    (L : Y → List X) (L' : Y' → List X')
    (e : src'.map f = src) (d : dst'.map g = dst) (hs : src.Nodup)
    (hL : ∀ j, (L' j).map f = L (g j)) (hB : ∀ j, B' j = B (g j))
    (r : AddressOrder X src (dst.flatMap L)) (r' : AddressOrder X' src' (dst'.flatMap L'))
    (p : ∀ j, fold 𝒮 Zₐ A (L j) ⟶ B j) (p' : ∀ j, fold 𝒮 Zₐ (A ∘ f) (L' j) ⟶ B' j)
    (_hp : ∀ j, HEq (p' j) (p (g j))) :
    let F := fold 𝒮 Zₐ A
    let S := (congrArg F e.symm).trans (std_fold_map A f src')
    let D := (congrArg (fun Z => fold 𝒮 Zₐ Z dst') (funext hB)).trans
      ((std_fold_map B g dst').symm.trans (congrArg (fold 𝒮 Zₐ B) d))
    eqToHom S ≫ AddressOrder.mapSum additiveStructure (A ∘ f) r' ≫
      rowsChart (A ∘ f) L' dst' ≫ act 𝒮 Zₐ p' dst' ≫ eqToHom D =
    AddressOrder.mapSum additiveStructure A r ≫ rowsChart A L dst ≫ act 𝒮 Zₐ p dst := by
  intro F S D
  let a := fun j => eqToHom (hB j)
  let P := fun j => p' j ≫ a j
  let E := congrArg (fun Z => fold 𝒮 Zₐ Z dst') (funext hB)
  let d' := (std_fold_map B g dst').symm.trans (congrArg (fold 𝒮 Zₐ B) d)
  let h := fun j => (std_fold_map A f (L' j)).symm.trans (congrArg F (hL j))
  let Z := fun j => eqToHom (h j) ≫ p (g j)
  let v : (dst'.flatMap L').map f = dst'.flatMap (L ∘ g) :=
    (List.map_flatMap (f:=f) (g:=L') (l:=dst')).trans
      (congrArg (fun L => dst'.flatMap L) (funext hL))
  let w : dst'.flatMap (L ∘ g) = dst.flatMap L :=
    (List.flatMap_map g L dst').symm.trans (congrArg (fun t => t.flatMap L) d)
  let q := (r'.relabel f).seq (castOrder v)
  have z : act 𝒮 Zₐ p' dst' ≫ eqToHom E = act 𝒮 Zₐ P dst' := by
    rw [← std_act_eqToHom hB dst']
    exact act_seq (S:=𝒮) (Z:=Zₐ) p' a dst'
  have eP : P = Z := funext fun j => heq_paste (h j) (hB j) (_hp j)
  change eqToHom S ≫ AddressOrder.mapSum additiveStructure (A ∘ f) r' ≫
      rowsChart (A ∘ f) L' dst' ≫ act 𝒮 Zₐ p' dst' ≫ eqToHom (E.trans d') = _
  rw [← eqToHom_trans E d']
  rw [reassoc_of% z, eP]
  have m := wordChart_retag A (B ∘ g) f src' L' (L ∘ g) dst' hL r' (fun j => p (g j))
  dsimp only at m
  have m' : AddressOrder.mapSum additiveStructure (A ∘ f) r' ≫ rowsChart (A ∘ f) L' dst' ≫ act 𝒮 Zₐ Z dst' =
      eqToHom (std_fold_map A f src').symm ≫ AddressOrder.mapSum additiveStructure A q ≫
        rowsChart A (L ∘ g) dst' ≫ act 𝒮 Zₐ (fun j => p (g j)) dst' := m
  rw [reassoc_of% m']
  have n := rowsChart_index_apply A L g p dst' d
  change rowsChart A (L ∘ g) dst' ≫ act 𝒮 Zₐ (fun j => p (g j)) dst' ≫ eqToHom d' =
    eqToHom (congrArg F w) ≫ rowsChart A L dst ≫ act 𝒮 Zₐ p dst at n
  rw [n]
  let r0 := (castOrder e.symm).seq (q.seq (castOrder w))
  have k : AddressOrder.mapSum additiveStructure A r0 = AddressOrder.mapSum additiveStructure A r :=
    tagged_permutation_coherent A hs r0 r
  change eqToHom S ≫ eqToHom (std_fold_map A f src').symm ≫ AddressOrder.mapSum additiveStructure A q ≫
    eqToHom (congrArg F w) ≫ rowsChart A L dst ≫ act 𝒮 Zₐ p dst = _
  rw [reassoc_of% eqToHom_trans S (std_fold_map A f src').symm]
  have E' : eqToHom (S.trans (std_fold_map A f src').symm) =
    AddressOrder.mapSum additiveStructure A (castOrder e.symm) := by rw [castOrder_map]
  rw [E']
  have rMap : AddressOrder.mapSum additiveStructure A r0 =
      AddressOrder.mapSum additiveStructure A (castOrder e.symm) ≫
        AddressOrder.mapSum additiveStructure A q ≫ eqToHom (congrArg F w) := by
    change _ ≫ _ ≫ AddressOrder.mapSum additiveStructure A (castOrder w) = _
    rw [castOrder_map A w]
  rw [← reassoc_of% rMap, k]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
