module
public import ContextualComposition.NativeIndependentFunctoriality
@[expose] public section

/-! Restrict the original independent native composite to each actual
final pair, and compare with the independent product of the two native
axis restrictions. No test augmentation at a common unit is needed. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}

def readPair {X Y : Type w} (x : List X) (y : List Y) :
    Fin x.length × Fin y.length → X × Y :=
  fun z => (x[z.1],y[z.2])

theorem readPair_word {X Y : Type w} (x : List X) (y : List Y) :
    ((List.finRange x.length).product (List.finRange y.length)).map (readPair x y) = x.product y := by
  change (List.product _ _).map (Prod.map (fun i : Fin x.length => x[i]) (fun i : Fin y.length => y[i])) = _
  rw [map_product_word, finRange_get, finRange_get]

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem independentPair_mem (A B : Family C) (t : Fin A.n × Fin B.n) : t ∈ independentWord A B :=
  by
  rcases t with ⟨x,y⟩
  change (x,y) ∈ (List.finRange A.n).flatMap (fun x => (List.finRange B.n).map (fun y => (x,y)))
  exact List.mem_flatMap.mpr ⟨x, List.mem_finRange _, List.mem_map.mpr ⟨y,List.mem_finRange _,rfl⟩⟩

noncomputable def independentPairIndex (A B : Family C) (t : Fin A.n × Fin B.n) : Fin (independentWord A B).length :=
  (wordPositions (independentWord A B) (independentWord_nodup A B)).symm ⟨t,independentPair_mem A B t⟩

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem independentPairIndex_read (A B : Family C) (t : Fin A.n × Fin B.n) :
    (independentWord A B)[independentPairIndex A B t] = t :=
  congrArg Subtype.val ((wordPositions (independentWord A B) (independentWord_nodup A B)).apply_symm_apply ⟨t,independentPair_mem A B t⟩)

set_option backward.isDefEq.respectTransparency false in
theorem independent_mid_positions
    {A B A' B' : Family C} (r : Hom ℙ A A') (s : Hom ℙ B B')
    (k : Fin (independentWord A' B').length) :
    let t := (independentWord A' B')[k]
    let a := fibreList r.addr t.1
    let b := fibreList s.addr t.2
    let f := Prod.map r.addr s.addr
    let g := wordCarrier f (independent_word_support r s) (independentWord_nodup A' B')
    let mid := ((List.finRange a.length).product (List.finRange b.length))
    mid.map (independentPairIndex A B ∘ readPair a b) = fibreList g k := by
  intro t a b f g mid
  let read := fun i : Fin (independentWord A B).length => (independentWord A B)[i]
  have hr : Function.Injective read := fun i j e => Fin.ext ((independentWord_nodup A B).getElem_inj.mp e)
  apply (List.map_inj_right (f:=read) (fun _ _ e => hr e)).mp
  rw [List.map_map]
  have kd : read ∘ (independentPairIndex A B ∘ readPair a b) = readPair a b :=
    funext fun u => independentPairIndex_read A B (readPair a b u)
  rw [kd]
  have h := wordCarrier_fibre f (independent_word_support r s) (independentWord_nodup A' B') k
  change (fibreList g k).map read = wordFibre (independentWord A B) f t at h
  rw [h, independent_get_fibre r s t]
  exact readPair_word a b

set_option backward.isDefEq.respectTransparency false in
theorem independent_restricted_fibre
    {A B A' B' A'' B'' : Family C}
    (p : Hom ℙ A A') (q : Hom ℙ B B') (r : Hom ℙ A' A'') (s : Hom ℙ B' B'')
    (i : Fin A''.n) (j : Fin B''.n)
    (t : Fin (fibreList r.addr i).length × Fin (fibreList s.addr j).length) :
    let a := fibreList (r.addr ∘ p.addr) i
    let b := fibreList (s.addr ∘ q.addr) j
    let u := (fibreList r.addr i)[t.1]
    let v := (fibreList s.addr j)[t.2]
    let p₀ := fibreRestrictNative p r.addr i
    let q₀ := fibreRestrictNative q s.addr j
    let w := ((List.finRange a.length).product (List.finRange b.length))
    (wordFibre w (Prod.map p₀.addr q₀.addr) t).map (readPair a b) =
      wordFibre (independentWord A B) (Prod.map p.addr q.addr) (u,v) := by
  intro a b u v p₀ q₀ w
  change (wordFibre (independentWord (wordFamily A.val a) (wordFamily B.val b)) (Prod.map p₀.addr q₀.addr) t).map
    (readPair a b) = _
  rw [independent_get_fibre p₀ q₀ t, independent_get_fibre p q (u,v)]
  change (List.product _ _).map (Prod.map (fun i : Fin a.length => a[i]) (fun i : Fin b.length => b[i])) = _
  rw [map_product_word]
  exact congrArg₂ List.product (restricted_native_fibre_read p r.addr i t.1)
    (restricted_native_fibre_read q s.addr j t.2)

set_option backward.isDefEq.respectTransparency false in
theorem wholeRestricted_comp {A B D : Family C} (p : Hom ℙ A B) (q : Hom ℙ B D) (k : Fin D.n) :
    let a := fibreList (q.addr ∘ p.addr) k
    let b := fibreList q.addr k
    wholeContinuation (fibreRestrictNative p q.addr k) ≫ eqToHom (wordTotalPin B.val b) ≫ q.cell k =
      eqToHom (wordTotalPin A.val a) ≫ (p.comp q).cell k := by
  intro a b
  have H := fibreRestrict_cell_total p q.addr k
  dsimp only at H
  let F := fibreRestrictNative p q.addr k
  have H' : wholeContinuation F ≫ eqToHom (wordTotalPin B.val b) =
      eqToHom (wordTotalPin A.val a) ≫ standardPushSplit p.addr q.addr A.val k ≫ standardPushMap q.addr p.cell k := by
    unfold wholeContinuation
    simp only [Category.assoc]
    exact H
  rw [reassoc_of% H']
  rfl


theorem pairFoldPin (T : Bi (coeff (C:=C))) (A B : Family C)
    (x : List (Fin A.n)) (y : List (Fin B.n)) :
    totalFold (independentFamily T (wordFamily A.val x) (wordFamily B.val y)) =
      fold 𝒮 Zₐ (independentLabels T A B) (x.product y) :=
  (wordTotalPin (independentLabels T (wordFamily A.val x) (wordFamily B.val y))
    (independentWord (wordFamily A.val x) (wordFamily B.val y))).trans
      ((std_fold_map (independentLabels T A B) (readPair x y)
        ((List.finRange x.length).product (List.finRange y.length))).symm.trans
        (congrArg (fold 𝒮 Zₐ (independentLabels T A B)) (readPair_word x y)))

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem bi_eqToHom {T : Bi (coeff (C:=C))} {a b a' b' : C}
    (p : a = a') (q : b = b') :
    T.map (eqToHom p) (eqToHom q) = eqToHom (congrArg₂ T.obj p q) := by
  cases p
  cases q
  exact T.map_id _ _

set_option backward.isDefEq.respectTransparency false in
theorem independentTotalChart_raw
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (A B : Family C) (x : List (Fin A.n)) (y : List (Fin B.n)) :
    independentTotalChart T R L (wordFamily A.val x) (wordFamily B.val y) ≫
      T.map (eqToHom (wordTotalPin A.val x)) (eqToHom (wordTotalPin B.val y)) =
      eqToHom (pairFoldPin T A B x y) ≫ rectWordChart (independentLabels T A B) x y ≫
        rowGather R L A.val B.val x y := by
  let X := wordFamily A.val x
  let Y := wordFamily B.val y
  let f := fun i : Fin x.length => x[i]
  let g := fun i : Fin y.length => y[i]
  let a := independentLabels T A B
  let b := independentLabels T X Y
  let lx := List.finRange x.length
  let ly := List.finRange y.length
  let w := independentWord X Y
  let p := wordTotalPin b w
  let u := (std_fold_map a (readPair x y) w).symm.trans (congrArg (fold 𝒮 Zₐ a) (readPair_word x y))
  have h := rectangleGather_map_heq R L A.val B.val f g lx ly
  dsimp only at h
  have k :
      HEq (rectWordChart b lx ly ≫ rowGather R L X.val Y.val lx ly)
        (rectWordChart a x y ≫ rowGather R L A.val B.val x y) := by
    have z {x₁ x₂ : List (Fin A.n)} {y₁ y₂ : List (Fin B.n)} (e : x₁ = x₂) (d : y₁ = y₂) :
      HEq (rectWordChart a x₁ y₁ ≫ rowGather R L A.val B.val x₁ y₁)
        (rectWordChart a x₂ y₂ ≫ rowGather R L A.val B.val x₂ y₂) := by
      cases e
      cases d
      rfl
    exact h.trans (z (finRange_get x) (finRange_get y))
  have H := heq_paste u (congrArg₂ T.obj (wordTotalPin A.val x) (wordTotalPin B.val y)) k
  rw [bi_eqToHom]
  change (eqToHom p ≫ rectWordChart b lx ly ≫ rowGather R L X.val Y.val lx ly) ≫
      eqToHom (congrArg₂ T.obj (wordTotalPin A.val x) (wordTotalPin B.val y)) =
    eqToHom (p.trans u) ≫ rectWordChart a x y ≫ rowGather R L A.val B.val x y
  simp only [Category.assoc]
  simp only [Category.assoc] at H
  rw [H, reassoc_of% eqToHom_trans p u]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
/-- The actual independent native composite at a final pair:
first restrict each axis to the corresponding final fibre, then
perform the two original second-stage whole-cell maps. -/
theorem independentComposite_restricted
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {A B A' B' A'' B'' : Family C}
    (p : Hom ℙ A A') (q : Hom ℙ B B') (r : Hom ℙ A' A'') (s : Hom ℙ B' B'')
    (k : Fin (independentWord A'' B'').length) :
    let t := (independentWord A'' B'')[k]
    let a := independentLabels T A B
    let c := independentLabels T A'' B''
    let f := Prod.map p.addr q.addr
    let g := Prod.map r.addr s.addr
    let gf := fun x hx => independent_word_support r s _ (independent_word_support p q x hx)
    let h := independentWord_nodup A'' B''
    let P := independentNativeWordMap T p q R L
    let Q := independentNativeWordMap T r s R L
    let a₁ := fibreList (r.addr ∘ p.addr) t.1
    let a₂ := fibreList (s.addr ∘ q.addr) t.2
    let b₁ := fibreList r.addr t.1
    let b₂ := fibreList s.addr t.2
    let P₀ := fibreRestrictNative p r.addr t.1
    let Q₀ := fibreRestrictNative q s.addr t.2
    let srcPin := (congrArg (fold 𝒮 Zₐ a) (independent_get_fibre (p.comp r) (q.comp s) t)).trans
      (pairFoldPin T A B a₁ a₂).symm
    readNativeWordCell a c (g ∘ f) gf h (P.comp Q)
      (wordCarrier_comp f g (independent_word_support p q) (independent_word_support r s)
        (independentWord_nodup A' B') h).symm k =
    eqToHom srcPin ≫ wholeContinuation (independentNativeWordMap T P₀ Q₀ R L) ≫
      independentTotalChart T R L (wordFamily A'.val b₁) (wordFamily B'.val b₂) ≫
        T.map (eqToHom (wordTotalPin A'.val b₁) ≫ r.cell t.1)
          (eqToHom (wordTotalPin B'.val b₂) ≫ s.cell t.2) := by
  intro t a c f g gf h P Q a₁ a₂ b₁ b₂ P₀ Q₀ srcPin
  let A₀ := wordFamily A.val a₁
  let B₀ := wordFamily B.val a₂
  let A₁ := wordFamily A'.val b₁
  let B₁ := wordFamily B'.val b₂
  let U := independentNativeWordMap T P₀ Q₀ R L
  let s₀ := independentWord A B
  let s₁ := independentWord A' B'
  let s₂ := independentWord A'' B''
  let w₀ := independentWord A₀ B₀
  let w₁ := independentWord A₁ B₁
  let input := wordFibre s₀ (g ∘ f) t
  let f₀ := readPair a₁ a₂
  let g₀ := independentPairIndex A' B' ∘ readPair b₁ b₂
  let addr := wordCarrier g (independent_word_support r s) h
  let ys := fibreList addr k
  let X := fun j : Fin s₁.length => independentLabels T A' B' s₁[j]
  let X' := independentLabels T A₁ B₁
  let F := Prod.map P₀.addr Q₀.addr
  let M := fun j : Fin s₁.length => wordFibre s₀ f s₁[j]
  let M' := wordFibre w₀ F
  let po := fun j : Fin s₁.length => independentWordCell T p q R L s₁[j]
  let qo := fun j : Fin s₂.length => independentWordCell T r s R L s₂[j]
  let pu := independentWordCell T P₀ Q₀ R L
  let read := fun i : Fin w₁.length => w₁[i]
  let ru0 := wordNativePartitionOrder F (independent_word_support P₀ Q₀) (independentWord_nodup A₁ B₁)
  let eu : (List.finRange w₁.length).flatMap (M' ∘ read) = w₁.flatMap M' :=
    (List.flatMap_map read M' (List.finRange w₁.length)).symm.trans
      (congrArg (fun x => x.flatMap M') (finRange_get w₁))
  let ru := ru0.seq (castOrder eu)
  have hd : w₁.map g₀ = ys := independent_mid_positions r s k
  have he : w₀.map f₀ = input :=
    (readPair_word a₁ a₂).trans (independent_get_fibre (p.comp r) (q.comp s) t).symm
  have hM (j : Fin A₁.n × Fin B₁.n) : (M' j).map f₀ = M (g₀ j) := by
    have H := independent_restricted_fibre p q r s t.1 t.2 j
    exact H.trans (congrArg (wordFibre s₀ f) (independentPairIndex_read A' B' (readPair b₁ b₂ j)).symm)
  have hB (j : Fin A₁.n × Fin B₁.n) : X' j = X (g₀ j) :=
    congrArg (independentLabels T A' B') (independentPairIndex_read A' B' (readPair b₁ b₂ j)).symm
  have hc (j : Fin A₁.n × Fin B₁.n) : HEq (pu j) (po (g₀ j)) := by
    have H := independent_restricted_cell_heq R L p q r s t.1 t.2 j
    have K {i j : Fin A'.n × Fin B'.n} (e : i = j) :
        HEq (independentWordCell T p q R L i) (independentWordCell T p q R L j) := by cases e; rfl
    exact H.trans (K (independentPairIndex_read A' B' (readPair b₁ b₂ j)).symm)
  let ee : (w₁.flatMap M').map f₀ = ys.flatMap M :=
    (List.map_flatMap (f:=f₀) (g:=M') (l:=w₁)).trans
      ((congrArg (fun x => w₁.flatMap x) (funext hM)).trans
        ((List.flatMap_map g₀ M w₁).symm.trans (congrArg (fun x => x.flatMap M) hd)))
  let ro := (castOrder he.symm).seq ((ru.relabel f₀).seq (castOrder ee))
  have rr := readCompositeWordCell_raw a (independentLabels T A' B') c f g
    (independent_word_support p q) (independent_word_support r s) (independentWord_nodup A' B') h
    (independentWord_nodup A B) po qo k ro
  change readNativeWordCell a c (g ∘ f) gf h (P.comp Q)
    (wordCarrier_comp f g (independent_word_support p q) (independent_word_support r s)
      (independentWord_nodup A' B') h).symm k =
    AddressOrder.mapSum additiveStructure a ro ≫ rowsChart a M ys ≫ act 𝒮 Zₐ po ys ≫
      eqToHom (wordCarrier_fibre_pin g (independent_word_support r s) h (independentLabels T A' B') k) ≫ qo k at rr
  rw [rr]
  have H := rawPartition_read_span a X X' f₀ g₀ input w₀ ys w₁ M M' he hd
    ((independentWord_nodup A B).filter _) hM hB ro ru po pu hc
  dsimp only at H
  let S := (congrArg (fold 𝒮 Zₐ a) he.symm).trans (std_fold_map a f₀ w₀)
  let D := (congrArg (fun Z => fold 𝒮 Zₐ Z w₁) (funext hB)).trans
      ((std_fold_map X g₀ w₁).symm.trans (congrArg (fold 𝒮 Zₐ X) hd))
  let Bpin := wordCarrier_fibre_pin g (independent_word_support r s) h (independentLabels T A' B') k
  change eqToHom S ≫ AddressOrder.mapSum additiveStructure (a ∘ f₀) ru ≫
    rowsChart (a ∘ f₀) M' w₁ ≫ act 𝒮 Zₐ pu w₁ ≫ eqToHom D = _ at H
  rw [← reassoc_of% H]
  let pin₀ := wordTotalPin (independentLabels T A₀ B₀) w₀
  let pin₁ := wordTotalPin X' w₁
  have K := wholeContinuation_native_raw_target F (independent_word_support P₀ Q₀)
    (independentWord_nodup A₀ B₀) (independentWord_nodup A₁ B₁) (independentLabels T A₀ B₀) X' pu ru
  change wholeContinuation U ≫ eqToHom pin₁ =
    eqToHom pin₀ ≫ AddressOrder.mapSum additiveStructure (a ∘ f₀) ru ≫
      rowsChart (a ∘ f₀) M' w₁ ≫ act 𝒮 Zₐ pu w₁ at K
  have S' : eqToHom S = eqToHom srcPin ≫ eqToHom pin₀ := by rw [eqToHom_trans]
  rw [S']
  simp only [Category.assoc]
  rw [← reassoc_of% K]
  let ep := congrArg (fold 𝒮 Zₐ (independentLabels T A' B')) (independent_get_fibre r s t)
  change eqToHom srcPin ≫ wholeContinuation U ≫ eqToHom pin₁ ≫ eqToHom D ≫ eqToHom Bpin ≫
    (eqToHom ep ≫ rectWordChart (independentLabels T A' B') b₁ b₂ ≫ rowGather R L A'.val B'.val b₁ b₂ ≫
      T.map (r.cell t.1) (s.cell t.2)) = _
  have pin : ((pin₁.trans D).trans Bpin).trans ep = pairFoldPin T A' B' b₁ b₂ := Subsingleton.elim _ _
  rw [reassoc_of% eqToHom_trans pin₁ D, reassoc_of% eqToHom_trans (pin₁.trans D) Bpin,
    reassoc_of% eqToHom_trans ((pin₁.trans D).trans Bpin) ep, pin]
  rw [← reassoc_of% independentTotalChart_raw R L A' B' b₁ b₂, bi_map_comp]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3800000 in
/-- Identity and composition are strict laws of the original ordered
independent binary native map, not just laws of its total scalar trace. -/
theorem independentNativeWordMap_comp
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' A'' B'' : Family C}
    (p : Hom ℙ A A') (q : Hom ℙ B B') (r : Hom ℙ A' A'') (s : Hom ℙ B' B'')
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    independentNativeWordMap T (p.comp r) (q.comp s) R L =
      (independentNativeWordMap T p q R L).comp (independentNativeWordMap T r s R L) := by
  let a := independentLabels T A B
  let c := independentLabels T A'' B''
  let f := Prod.map p.addr q.addr
  let g := Prod.map r.addr s.addr
  let w := independentWord A'' B''
  let hf := independent_word_support p q
  let hg := independent_word_support r s
  let F := g ∘ f
  let h := independentWord_nodup A'' B''
  let gf := fun x hx => hg _ (hf x hx)
  let P := independentNativeWordMap T p q R L
  let Q := independentNativeWordMap T r s R L
  let edge := (wordCarrier_comp f g hf hg (independentWord_nodup A' B') h).symm
  let p' := readNativeWordCell a c F gf h (P.comp Q) edge
  let q' := fun k : Fin w.length => independentWordCell T (p.comp r) (q.comp s) R L w[k]
  have hCell (k : Fin w.length) : p' k = q' k := by
    let t := w[k]
    let a₁ := fibreList (r.addr ∘ p.addr) t.1
    let a₂ := fibreList (s.addr ∘ q.addr) t.2
    let b₁ := fibreList r.addr t.1
    let b₂ := fibreList s.addr t.2
    let P₀ := fibreRestrictNative p r.addr t.1
    let Q₀ := fibreRestrictNative q s.addr t.2
    let b := independentLabels T A' B'
    let e := congrArg (fold 𝒮 Zₐ a) (independent_get_fibre (p.comp r) (q.comp s) t)
    let pin := pairFoldPin T A B a₁ a₂
    let u := eqToHom (wordTotalPin A'.val b₁) ≫ r.cell t.1
    let v := eqToHom (wordTotalPin B'.val b₂) ≫ s.cell t.2
    let H := independentTotalChart T R L (wordFamily A.val a₁) (wordFamily B.val a₂)
    let K := independentTotalChart T R L (wordFamily A'.val b₁) (wordFamily B'.val b₂)
    have j := independentComposite_restricted R L p q r s k
    dsimp only at j
    change p' k = eqToHom (e.trans pin.symm) ≫ wholeContinuation (independentNativeWordMap T P₀ Q₀ R L) ≫
      K ≫ T.map u v at j
    rw [j]
    have j' := independentWholeContinuation R L N NR NL P₀ Q₀ _hl _hr
    change wholeContinuation (independentNativeWordMap T P₀ Q₀ R L) ≫ K =
      H ≫ T.map (wholeContinuation P₀) (wholeContinuation Q₀) at j'
    rw [reassoc_of% j', bi_map_comp]
    have e₁ := wholeRestricted_comp p r t.1
    have e₂ := wholeRestricted_comp q s t.2
    change wholeContinuation P₀ ≫ u = eqToHom (wordTotalPin A.val a₁) ≫ (p.comp r).cell t.1 at e₁
    change wholeContinuation Q₀ ≫ v = eqToHom (wordTotalPin B.val a₂) ≫ (q.comp s).cell t.2 at e₂
    rw [e₁,e₂,← bi_map_comp]
    have cr := independentTotalChart_raw R L A B a₁ a₂
    change H ≫ T.map (eqToHom (wordTotalPin A.val a₁)) (eqToHom (wordTotalPin B.val a₂)) = _ at cr
    rw [reassoc_of% cr, reassoc_of% eqToHom_trans]
    change eqToHom _ ≫ _ = _
    rfl
  change wordNativeMap F gf h a c q' = P.comp Q
  rw [show q' = p' from (funext hCell).symm]
  exact readNativeWordCell_reassemble a c F gf h (P.comp Q) edge

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
