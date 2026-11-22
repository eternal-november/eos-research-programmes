module
public import ContextualComposition.NativeRawParentBlocks

@[expose] public section
/-! Exact interaction between independent multiplicative gathers and
arbitrary additive row partitions. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {T : Bi (coeff (C:=C))}

set_option backward.isDefEq.respectTransparency false in
theorem right_gather_rows (R : Gather 𝒮 T Zₐ) (a : C) [(rightFactor (T:=T) a).LaxBraided]
    (ha : SameRightGather R a) {X Y : Type w} (A : X → C) (L : Y → List X) (ys : List Y) :
    rowsChart (fun x => T.obj (A x) a) L ys ≫
      act 𝒮 Zₐ (fun y => DependentFibre.gather R A a (L y)) ys ≫
      DependentFibre.gather R (fun y => fold 𝒮 Zₐ A (L y)) a ys =
    DependentFibre.gather R A a (ys.flatMap L) ≫ T.map (rowsChart A L ys) (𝟙 a) := by
  simpa only [rightFactor_sameCollect R ha] using collect_rows (rightFactor (T:=T) a) A L ys

set_option backward.isDefEq.respectTransparency false in
theorem left_gather_rows (L : LeftGather 𝒮 T Zₐ) (a : C) [(leftFactor T a).LaxBraided]
    (ha : SameLeftGather T a L) {X Y : Type w} (A : X → C) (M : Y → List X) (ys : List Y) :
    rowsChart (fun x => T.obj a (A x)) M ys ≫
      act 𝒮 Zₐ (fun y => Lin.collect (Lin.left L a) A (M y)) ys ≫
      Lin.collect (Lin.left L a) (fun y => fold 𝒮 Zₐ A (M y)) ys =
    Lin.collect (Lin.left L a) A (ys.flatMap M) ≫ T.map (𝟙 a) (rowsChart A M ys) := by
  simpa only [leftFactor_sameCollect T a L ha] using collect_rows (leftFactor T a) A M ys


/-- The same occurrence-first coefficient computation, allowing the index
universe to differ from the coefficient universe. -/
def independentGroupedGather (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y I J : Type w}
    (A : X → C) (B : Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :=
  (coeff (C:=C)).seq
    (act 𝒮 Zₐ (fun i => raggedRowGather R L A (rows i) js cols (fun _ => B)) is)
    (DependentFibre.gather R (fun i => fold 𝒮 Zₐ A (rows i))
      (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B (cols j)) js) is)

theorem independentGroupedGather_eq (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y I J : Type u} (A : X → C) (B : Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J) :
    independentGroupedGather R L A B rows cols is js =
      occurrenceFirst R L (fun _ => A) (fun _ => B) is js rows cols := rfl

set_option backward.isDefEq.respectTransparency false in
theorem occurrenceFirst_partition
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {X Y I J : Type w}
    (A : X → C) (B : Y → C) (rows : I → List X) (cols : J → List Y)
    (is : List I) (js : List J)
    [∀ x : X, (leftFactor T (A x)).LaxBraided]
    [(rightFactor (T:=T) (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B (cols j)) js)).LaxBraided]
    (hl : ∀ x, SameLeftGather T (A x) L)
    (hr : SameRightGather R (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B (cols j)) js)) :
    act 𝒮 Zₐ (fun x => rowsChart (fun y => T.obj (A x) (B y)) cols js) (is.flatMap rows) ≫
      rowsChart (fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => T.obj (A x) (B y)) (cols j)) js) rows is ≫
      independentGroupedGather R L A B rows cols is js =
    rowGather R L A B (is.flatMap rows) (js.flatMap cols) ≫
      T.map (rowsChart A rows is) (rowsChart B cols js) := by
  let BX := fun j => fold 𝒮 Zₐ B (cols j)
  let E := fold 𝒮 Zₐ BX js
  let xw := is.flatMap rows
  let yw := js.flatMap cols
  let U := fold 𝒮 Zₐ B yw
  let S₁ := fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun y => T.obj (A x) (B y)) (cols j)) js
  let h := fun x => rowsChart (fun y => T.obj (A x) (B y)) cols js
  let g := fun x => act 𝒮 Zₐ (fun j => Lin.collect (Lin.left L (A x)) B (cols j)) js ≫
    Lin.collect (Lin.left L (A x)) BX js
  let f := fun x => Lin.collect (Lin.left L (A x)) B yw
  let k := rowsChart B cols js
  let d := fun x => T.map (𝟙 (A x)) k
  let v := rowsChart A rows is
  let a := DependentFibre.gather R A E xw
  let b := DependentFibre.gather R A U xw
  let c := DependentFibre.gather R (fun i => fold 𝒮 Zₐ A (rows i)) E is
  let a₀ := fun i => DependentFibre.gather R A E (rows i)
  have wg (i : I) :
      raggedRowGather R L A (rows i) js cols (fun _ => B) =
        act 𝒮 Zₐ g (rows i) ≫ a₀ i := by
    unfold raggedRowGather rowGather
    rw [← (coeff (C:=C)).assoc]
    exact congrArg (fun p => p ≫ a₀ i)
      (act_seq 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun j => Lin.collect (Lin.left L (A x)) B (cols j)) js)
        (fun x => Lin.collect (Lin.left L (A x)) BX js) (rows i))
  have ee : rowsChart S₁ rows is ≫ independentGroupedGather R L A B rows cols is js =
      act 𝒮 Zₐ g xw ≫ a ≫ T.map v (𝟙 E) := by
    unfold independentGroupedGather
    change rowsChart S₁ rows is ≫ act 𝒮 Zₐ (fun i => raggedRowGather R L A (rows i) js cols (fun _ => B)) is ≫ c = _
    have e₁ := congrArg (fun q => act 𝒮 Zₐ q is) (funext wg)
    have e₂ := act_seq 𝒮 Zₐ (fun i => act 𝒮 Zₐ g (rows i)) a₀ is
    have e₃ := (rowsChart_natural rows g is).symm
    have e₄ := right_gather_rows R E hr A rows is
    rw [e₁, ← e₂]
    simp only [Category.assoc]
    rw [← Category.assoc (rowsChart S₁ rows is), e₃]
    simp only [Category.assoc]
    exact congrArg (fun q => act 𝒮 Zₐ g xw ≫ q) e₄
  have kg (x : X) : h x ≫ g x = f x ≫ d x := by
    have e := left_gather_rows L (A x) (hl x) B cols js
    simpa only [h,g,f,d,k,yw,Category.assoc] using e
  have kk : act 𝒮 Zₐ h xw ≫ act 𝒮 Zₐ g xw = act 𝒮 Zₐ f xw ≫ act 𝒮 Zₐ d xw :=
    (act_seq 𝒮 Zₐ h g xw).trans ((congrArg (fun q => act 𝒮 Zₐ q xw) (funext kg)).trans (act_seq 𝒮 Zₐ f d xw).symm)
  have gnat : act 𝒮 Zₐ d xw ≫ a = b ≫ T.map (𝟙 (fold 𝒮 Zₐ A xw)) k := (gather_nat R A k xw).symm
  have mul : T.map (𝟙 (fold 𝒮 Zₐ A xw)) k ≫ T.map v (𝟙 E) = T.map v k := by
    have z :=
      (T.map_seq (𝟙 (fold 𝒮 Zₐ A xw)) v k (𝟙 E)).symm
    have e : (𝟙 (fold 𝒮 Zₐ A xw)) ≫ v = v := Category.id_comp v
    have e' : k ≫ 𝟙 E = k := Category.comp_id k
    change _ = T.map (𝟙 _ ≫ v) (k ≫ 𝟙 E) at z
    rw [e, e'] at z
    exact z
  change act 𝒮 Zₐ h xw ≫ (rowsChart S₁ rows is ≫ independentGroupedGather R L A B rows cols is js) =
    (act 𝒮 Zₐ f xw ≫ b) ≫ T.map v k
  rw [ee, ← Category.assoc (act 𝒮 Zₐ h xw), kk]
  simp only [Category.assoc]
  rw [← Category.assoc (act 𝒮 Zₐ d xw), gnat]
  simp only [Category.assoc]
  rw [mul]



set_option backward.isDefEq.respectTransparency false in
/-- Independent reorderings are applied on raw tagged axes, not on coefficient
labels. A rectangular native comparison absorbs exactly these reorderings. -/
theorem independent_gather_order (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type w} (A : X → C) (B : Y → C) {xs xs' : List X} {ys ys' : List Y}
    (p : AddressOrder X xs xs') (q : AddressOrder Y ys ys')
    [∀ x : X, (leftFactor T (A x)).LaxBraided]
    [(rightFactor (T:=T) (fold 𝒮 Zₐ B ys')).LaxBraided]
    (hl : ∀ x, SameLeftGather T (A x) L)
    (hr : SameRightGather R (fold 𝒮 Zₐ B ys')) :
    act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (fun y => T.obj (A x) (B y)) q) xs ≫
      AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun y => T.obj (A x) (B y)) ys') p ≫
      rowGather R L A B xs' ys' =
    rowGather R L A B xs ys ≫
      T.map (AddressOrder.mapSum additiveStructure A p) (AddressOrder.mapSum additiveStructure B q) := by
  let U := fold 𝒮 Zₐ B ys
  let E := fold 𝒮 Zₐ B ys'
  let l := fun x => Lin.collect (Lin.left L (A x)) B ys
  let r := fun x => Lin.collect (Lin.left L (A x)) B ys'
  let k := AddressOrder.mapSum additiveStructure B q
  let v := AddressOrder.mapSum additiveStructure A p
  let h := fun x => AddressOrder.mapSum additiveStructure (fun y => T.obj (A x) (B y)) q
  let d := fun x => T.map (𝟙 (A x)) k
  let t := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun y => T.obj (A x) (B y)) ys') p
  let s := AddressOrder.mapSum additiveStructure (fun x => T.obj (A x) E) p
  let g := DependentFibre.gather R A E xs'
  let g₀ := DependentFibre.gather R A E xs
  let f := DependentFibre.gather R A U xs
  change act 𝒮 Zₐ h xs ≫ t ≫ (act 𝒮 Zₐ r xs' ≫ g) = (act 𝒮 Zₐ l xs ≫ f) ≫ T.map v k
  have enat : t ≫ act 𝒮 Zₐ r xs' = act 𝒮 Zₐ r xs ≫ s :=
    (AddressOrder.natural additiveNaturality r p).symm
  have er : s ≫ g = g₀ ≫ T.map v (𝟙 E) := by
    let F := rightFactor (T:=T) E
    have h : SameRightGather R E := hr
    have H := collect_order F A p
    change s ≫ Lin.collect (linearFunctor F) A xs' =
      Lin.collect (linearFunctor F) A xs ≫ T.map v (𝟙 E) at H
    have e := rightFactor_sameCollect R h A xs'
    have e₀ := rightFactor_sameCollect R h A xs
    rw [e, e₀] at H
    exact H
  have el (x : X) : h x ≫ r x = l x ≫ d x := by
    simpa only [leftFactor_sameCollect T (A x) L (hl x)] using collect_order (leftFactor T (A x)) B q
  have ea : act 𝒮 Zₐ h xs ≫ act 𝒮 Zₐ r xs = act 𝒮 Zₐ l xs ≫ act 𝒮 Zₐ d xs :=
    (act_seq 𝒮 Zₐ h r xs).trans ((congrArg (fun u => act 𝒮 Zₐ u xs) (funext el)).trans (act_seq 𝒮 Zₐ l d xs).symm)
  have eg : act 𝒮 Zₐ d xs ≫ g₀ = f ≫ T.map (𝟙 (fold 𝒮 Zₐ A xs)) k :=
    (gather_nat R A k xs).symm
  have mul : T.map (𝟙 (fold 𝒮 Zₐ A xs)) k ≫ T.map v (𝟙 E) = T.map v k := by
    have z := (T.map_seq (𝟙 (fold 𝒮 Zₐ A xs)) v k (𝟙 E)).symm
    have e : (𝟙 (fold 𝒮 Zₐ A xs)) ≫ v = v := Category.id_comp v
    have e' : k ≫ 𝟙 E = k := Category.comp_id k
    change _ = T.map (𝟙 _ ≫ v) (k ≫ 𝟙 E) at z
    rw [e, e'] at z
    exact z
  simp only [Category.assoc]
  rw [reassoc_of% enat, er, ← Category.assoc (act 𝒮 Zₐ h xs), ea]
  simp only [Category.assoc]
  rw [← Category.assoc (act 𝒮 Zₐ d xs), eg]
  simp only [Category.assoc]
  rw [mul]


local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
/-- An independent rectangle built from two actual carrier-changing
augmented maps preserves the coefficient augmentation. All reorder and
regrouping maps here are their native whole-fibre partitions. -/
theorem independent_native_partition_preserves
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {A B A' B' : Family C} {I : C}
    {δ : totalFold A ⟶ I} {η : totalFold B ⟶ I}
    {δ' : totalFold A' ⟶ I} {η' : totalFold B' ⟶ I}
    (p : AugHom ℙ (totalAug A δ) (totalAug A' δ'))
    (q : AugHom ℙ (totalAug B η) (totalAug B' η'))
    [∀ x : Fin A.n, (leftFactor T (A.val x)).LaxBraided]
    [rr : (rightFactor (T:=T)
      (fold 𝒮 Zₐ B.val ((List.finRange B'.n).flatMap (fibreList q.native.addr)))).LaxBraided]
    [rs : (rightFactor (T:=T)
      (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList q.native.addr j)) (List.finRange B'.n))).LaxBraided]
    (hl : ∀ x : Fin A.n, SameLeftGather T (A.val x) L)
    (hr : SameRightGather R (fold 𝒮 Zₐ B.val ((List.finRange B'.n).flatMap (fibreList q.native.addr))))
    (hr' : SameRightGather R (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ B.val (fibreList q.native.addr j)) (List.finRange B'.n))) :
    let xs := List.finRange A.n
    let ys := List.finRange B.n
    let sx := List.finRange A'.n
    let sy := List.finRange B'.n
    let U := fibreList p.native.addr
    let V := fibreList q.native.addr
    let P := totalPartitionOrder p.native.addr
    let Q := totalPartitionOrder q.native.addr
    let xw := sx.flatMap U
    let yw := sy.flatMap V
    let H := fun x y => T.obj (A.val x) (B.val y)
    act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (H x) Q) xs ≫
      AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (H x) yw) P ≫
      act 𝒮 Zₐ (fun x => rowsChart (H x) V sy) xw ≫
      rowsChart (fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (H x) (V j)) sy) U sx ≫
      independentGroupedGather R L A.val B.val U V sx sy ≫
      T.map (act 𝒮 Zₐ p.native.cell sx) (act 𝒮 Zₐ q.native.cell sy) ≫ T.map δ' η' =
    rowGather R L A.val B.val xs ys ≫ T.map δ η := by
  intro xs ys sx sy U V P Q xw yw H
  let p₀ : Hom ℙ A A' := p.native
  let q₀ : Hom ℙ B B' := q.native
  let s := AddressOrder.mapSum additiveStructure A.val P
  let t := AddressOrder.mapSum additiveStructure B.val Q
  let e := rowsChart A.val U sx
  let f := rowsChart B.val V sy
  let g := act 𝒮 Zₐ p₀.cell sx
  let h := act 𝒮 Zₐ q₀.cell sy
  let X := act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (H x) Q) xs
  let Y := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (H x) yw) P
  let D := act 𝒮 Zₐ (fun x => rowsChart (H x) V sy) xw
  let F := rowsChart (fun x => fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (H x) (V j)) sy) U sx
  let K := independentGroupedGather R L A.val B.val U V sx sy
  let r := rowGather R L A.val B.val xw yw
  let v := rowGather R L A.val B.val xs ys
  change X ≫ Y ≫ D ≫ F ≫ K ≫ T.map g h ≫ T.map δ' η' = v ≫ T.map δ η
  have d₁ : D ≫ F ≫ K = r ≫ T.map e f :=
    @occurrenceFirst_partition C _ _ _ T R L (Fin A.n) (Fin B.n) (Fin A'.n) (Fin B'.n)
      A.val B.val U V sx sy _ rs hl hr'
  have d₂ : X ≫ Y ≫ r = v ≫ T.map s t :=
    @independent_gather_order C _ _ _ T R L (Fin A.n) (Fin B.n) A.val B.val xs xw ys yw P Q _ rr hl hr
  have ep : s ≫ e ≫ g ≫ δ' = δ := by
    have H : wholeContinuation p₀ ≫ δ' = δ := wholeContinuation_preserves p
    simpa only [wholeContinuation, Category.assoc] using H
  have eq : t ≫ f ≫ h ≫ η' = η := by
    have H : wholeContinuation q₀ ≫ η' = η := wholeContinuation_preserves q
    simpa only [wholeContinuation, Category.assoc] using H
  have m : T.map s t ≫ T.map e f ≫ T.map g h ≫ T.map δ' η' = T.map δ η := by
    change (coeff (C:=C)).seq (T.map s t) ((coeff (C:=C)).seq (T.map e f)
      ((coeff (C:=C)).seq (T.map g h) (T.map δ' η'))) = _
    rw [← T.map_seq, ← T.map_seq, ← T.map_seq]
    change T.map (s ≫ e ≫ g ≫ δ') (t ≫ f ≫ h ≫ η') = _
    rw [ep, eq]
  rw [reassoc_of% d₁, reassoc_of% d₂, m]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
