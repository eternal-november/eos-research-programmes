module
public import ContextualComposition.NativeGridRetag
@[expose] public section
/-! Exact selected parent-block presentation retaining its original source
parent witnesses and each actual target child position. -/
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

abbrev selectedBlockWord (a : X') := dependentWord (D.slice a) (us ∘ Subtype.val)
abbrev selectedChildAddr (a : X') (r : D.Slice a × U) := D.child r.1.val r.2

theorem selectedChild_support (a : X') :
    ∀ p ∈ selectedBlockWord D a, selectedChildAddr D a p ∈ us' a := by
  intro p hp
  have h := (dependentWord_mem (D.slice a) (us ∘ Subtype.val) p).mp hp
  exact D.innerSlice_support p.1 p.2 h.2

theorem selectedChild_fibre (a : X') (t : U') :
    wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t =
      dependentWord (D.slice a) (D.terms a t) := by
  simp only [wordFibre, dependentWord, List.filter_flatMap, List.filter_map]
  rfl

def selectedChildColumnExpr (a : X') (t : U') : GridExpr (D.Slice a × U) :=
  dependentExpr (D.slice a) (D.terms a t)

theorem selectedChildColumn_leaves (a : X') (t : U') :
    (selectedChildColumnExpr D a t).leaves =
      wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t := by
  rw [selectedChild_fibre]
  exact dependentExpr_leaves _ _

def selectedChildBlockCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (a : X') (ha : a ∈ xs') (t : U') (ht : t ∈ us' a) :
    fold 𝒮 Zₐ (fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p))
      (wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t) ⟶ T.obj (V' a) (W' a t) :=
  let A := fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p)
  eqToHom (congrArg (fold 𝒮 Zₐ A) (selectedChildColumn_leaves D a t).symm) ≫
    compressGrid A (selectedChildColumnExpr D a t) ≫ eqToHom (dependentExpr_evalRaw (T:=T) D a t) ≫
    act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x t ht) (D.slice a) ≫
    DependentFibre.gather R (D.parentVal a) (W' a t) (D.slice a) ≫
    T.map (D.locOuter a ha) (𝟙 (W' a t))

noncomputable def selectedChildBlockMap (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (a : X') (ha : a ∈ xs') (h : (us' a).Nodup) :
    Hom ℙ (wordFamily (fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p)) (selectedBlockWord D a))
      (wordFamily (fun t => T.obj (V' a) (W' a t)) (us' a)) :=
  wordNativeMap (selectedChildAddr D a) (selectedChild_support D a) h
    (fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p))
    (fun t => T.obj (V' a) (W' a t))
    (fun j => selectedChildBlockCell D R L a ha (us' a)[j] (List.getElem_mem _))

section Matrix
variable (a : X')
abbrev selectedPositions := List.finRange (us' a).length
abbrev selectedFibreAt (x : D.Slice a) (j : Fin (us' a).length) :=
  wordFibre (us x.val) (D.child x.val) (us' a)[j]

abbrev selectedMatrixLabels := fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p)

def selectedRowExpr : GridExpr (D.Slice a × U) :=
  leafPartitionMatrix (fun x y => (x,y)) (selectedFibreAt D a) (D.slice a) (selectedPositions (us':=us') a)

def selectedColumnExpr : GridExpr (D.Slice a × U) :=
  GridExpr.over (fun j : Fin (us' a).length => selectedChildColumnExpr D a (us' a)[j])
    (selectedPositions (us':=us') a)

def selectedExchange : GridCircuit (D.Slice a × U) (selectedRowExpr D a) (selectedColumnExpr D a) :=
  GridCircuit.transpose
    (fun (x : D.Slice a) (j : Fin (us' a).length) =>
      GridExpr.over (fun y => GridExpr.leaf (x,y)) (selectedFibreAt D a x j))
    (selectedPositions (us':=us') a) (D.slice a)

theorem selectedColumn_leaves :
    (selectedColumnExpr D a).leaves = (selectedPositions (us':=us') a).flatMap
      (fun j : Fin (us' a).length => wordFibre (selectedBlockWord D a) (selectedChildAddr D a) (us' a)[j]) := by
  unfold selectedColumnExpr
  rw [GridExpr.leaves_over]
  exact congrArg (fun k => (selectedPositions (us':=us') a).flatMap k)
    (funext (fun j : Fin (us' a).length => selectedChildColumn_leaves D a (us' a)[j]))

abbrev selectedMatrixCell (x : D.Slice a) (j : Fin (us' a).length) :=
  fold 𝒮 Zₐ (fun y => T.obj (V x.val) (W x.val y)) (selectedFibreAt D a x j)

theorem selectedRow_eval :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (selectedMatrixLabels (T:=T) D a) (selectedRowExpr D a) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (selectedMatrixCell (T:=T) D a x) (selectedPositions (us':=us') a))
        (D.slice a) :=
  leafPartitionMatrix_eval (selectedMatrixLabels (T:=T) D a) _ _ _ _

theorem selectedColumn_eval :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (selectedMatrixLabels (T:=T) D a) (selectedColumnExpr D a) =
      fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ (fun x => selectedMatrixCell (T:=T) D a x j) (D.slice a))
        (selectedPositions (us':=us') a) :=
  (GridExpr.eval_over _ _ _).trans (congrArg (fun k => fold 𝒮 Zₐ k (selectedPositions (us':=us') a))
    (funext fun j : Fin (us' a).length => dependentExpr_evalRaw (T:=T) D a (us' a)[j]))

set_option backward.isDefEq.respectTransparency false in
theorem selectedExchange_eval :
    HEq (GridCircuit.eval (symmetricCross (C:=C)) (selectedMatrixLabels (T:=T) D a) (selectedExchange D a))
      (transposeBlock (symmetricCross (C:=C)) (selectedMatrixCell (T:=T) D a)
        (selectedPositions (us':=us') a) (D.slice a)) := by
  let M := symmetricCross (C:=C)
  let A := selectedMatrixLabels (T:=T) D a
  let E := fun (x : D.Slice a) (j : Fin (us' a).length) =>
    GridExpr.over (fun y => GridExpr.leaf (x,y)) (selectedFibreAt D a x j)
  let s := D.slice a
  let ts := selectedPositions (us':=us') a
  let P := selectedMatrixCell (T:=T) D a
  have K : (fun x j => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (E x j)) = P := by
    funext x j
    exact GridExpr.eval_over _ _ _
  have φ (B Q : D.Slice a → Fin (us' a).length → C) (h : B = Q) :
      HEq (transposeBlock M B ts s) (transposeBlock M Q ts s) := by cases h; rfl
  exact (GridCircuit.transpose_eval M A E ts s).trans (φ _ _ K)

def selectedColumnPureCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (ha : a ∈ xs') (j : Fin (us' a).length) :
    fold 𝒮 Zₐ (fun x => selectedMatrixCell (T:=T) D a x j) (D.slice a) ⟶
      T.obj (V' a) (W' a (us' a)[j]) :=
  let t := (us' a)[j]
  act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x t (List.getElem_mem _)) (D.slice a) ≫
    DependentFibre.gather R (D.parentVal a) (W' a t) (D.slice a) ≫
    T.map (D.locOuter a ha) (𝟙 (W' a t))

set_option backward.isDefEq.respectTransparency false in
theorem selectedColumn_chart (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (ha : a ∈ xs') :
    let A := selectedMatrixLabels (T:=T) D a
    let ts := selectedPositions (us':=us') a
    let w := fun j : Fin (us' a).length => wordFibre (selectedBlockWord D a) (selectedChildAddr D a) (us' a)[j]
    compressGrid A (selectedColumnExpr D a) ≫ eqToHom (selectedColumn_eval (T:=T) D a) ≫
      act 𝒮 Zₐ (selectedColumnPureCell D a R L ha) ts =
    eqToHom (congrArg (fold 𝒮 Zₐ A) (selectedColumn_leaves D a)) ≫ rowsChart A w ts ≫
      act 𝒮 Zₐ (fun j : Fin (us' a).length => selectedChildBlockCell D R L a ha (us' a)[j] (List.getElem_mem _)) ts := by
  intro A ts w
  let F := fold 𝒮 Zₐ A
  let C₀ := fun j : Fin (us' a).length => selectedChildColumnExpr D a (us' a)[j]
  let L₀ := fun j => (C₀ j).leaves
  let h := fun j : Fin (us' a).length => selectedChildColumn_leaves D a (us' a)[j]
  let g : ∀ j : Fin (us' a).length, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (C₀ j) ⟶
      fold 𝒮 Zₐ (fun x => selectedMatrixCell (T:=T) D a x j) (D.slice a) :=
    fun j => eqToHom (dependentExpr_evalRaw (T:=T) D a (us' a)[j])
  let p := selectedColumnPureCell D a R L ha
  let s := fun j => compressGrid A (C₀ j)
  let f := fun j : Fin (us' a).length => selectedChildBlockCell D R L a ha (us' a)[j] (List.getElem_mem _)
  let e := congrArg F (GridExpr.leaves_over C₀ ts)
  let e' := congrArg F (congrArg (fun k => ts.flatMap k) (funext h))
  let c := fun j => eqToHom (congrArg F (h j))
  have b : eqToHom (selectedColumn_eval (T:=T) D a) =
      eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A C₀ ts) ≫ act 𝒮 Zₐ g ts := by
    rw [std_act_eqToHom, eqToHom_trans]
  have m (j : Fin (us' a).length) : s j ≫ g j ≫ p j = c j ≫ f j := by
    let k := congrArg F (h j)
    change s j ≫ g j ≫ p j = eqToHom k ≫ eqToHom k.symm ≫ s j ≫ g j ≫ p j
    have hh : eqToHom k ≫ eqToHom k.symm = 𝟙 _ := by rw [eqToHom_trans]; rfl
    rw [reassoc_of% hh]
  have H : act 𝒮 Zₐ s ts ≫ act 𝒮 Zₐ g ts ≫ act 𝒮 Zₐ p ts = act 𝒮 Zₐ c ts ≫ act 𝒮 Zₐ f ts := by
    exact (congrArg (fun k => act 𝒮 Zₐ s ts ≫ k) (act_seq 𝒮 Zₐ g p ts)).trans
      ((act_seq 𝒮 Zₐ s (fun j => g j ≫ p j) ts).trans
        ((congrArg (fun k => act 𝒮 Zₐ k ts) (funext m)).trans (act_seq 𝒮 Zₐ c f ts).symm))
  have H₀ : rowsChart A L₀ ts ≫ act 𝒮 Zₐ c ts = eqToHom e' ≫ rowsChart A w ts := rowsChart_rows_congr A h ts
  rw [b]
  simp only [Category.assoc]
  rw [← Category.assoc (compressGrid A (selectedColumnExpr D a))]
  change (compressGrid A (GridExpr.over C₀ ts) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A C₀ ts)) ≫
    (act 𝒮 Zₐ g ts ≫ act 𝒮 Zₐ p ts) = _
  rw [compressGrid_over]
  simp only [Category.assoc]
  change eqToHom e ≫ rowsChart A L₀ ts ≫ (act 𝒮 Zₐ s ts ≫ act 𝒮 Zₐ g ts ≫ act 𝒮 Zₐ p ts) =
    eqToHom (e.trans e') ≫ rowsChart A w ts ≫ act 𝒮 Zₐ f ts
  rw [H, reassoc_of% H₀, reassoc_of% eqToHom_trans e e']

def selectedParentSourceAugCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {I : C} (J : UnitCompat R I) (ha : a ∈ xs')
    (δ : ∀ x : X, fold 𝒮 Zₐ (W x) (us x) ⟶ I) :
    fold 𝒮 Zₐ (selectedMatrixLabels (T:=T) D a) (selectedBlockWord D a) ⟶ V' a :=
  taggedRaggedRows (selectedMatrixLabels (T:=T) D a) (fun x y => (x,y)) (us ∘ Subtype.val) (D.slice a) ≫
    act 𝒮 Zₐ (fun x : D.Slice a => (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫
      T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val)) (D.slice a) ≫ D.locOuter a ha

/-- Position chart of the target row. Both the additive total transported
back to tags and the target's actual continuation augmentation are used. -/
def selectedParentTargetAugCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {I : C} (J : UnitCompat R I)
    (δ : fold 𝒮 Zₐ (W' a) (us' a) ⟶ I) :
    fold 𝒮 Zₐ (fun t => T.obj (V' a) (W' a t)) (us' a) ⟶ V' a :=
  eqToHom (wordTotalPin (fun t => T.obj (V' a) (W' a t)) (us' a)).symm ≫
    (Lin.left L (V' a)).collect (fun j : Fin (us' a).length => W' a (us' a)[j]) (selectedPositions (us':=us') a) ≫
    T.map (𝟙 (V' a)) (eqToHom (wordTotalPin (W' a) (us' a)) ≫ δ) ≫ J.ρ (V' a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
/-- Actual augmented native map on the selected parent block. Its cells
are the original selected child's coefficients, the target continuation
is whole, and the output is the opaque target parent resource. -/
noncomputable def selectedParentBlockAugMap
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    {I : C} (J : UnitCompat R I)
    {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (hp : D.Preserves hn hk δ δ' ε ε') (ha : a ∈ xs')
    (hh : (us' a).Nodup) (hx : ∀ x : D.Slice a, (us x.val).Nodup)
    (hw : (selectedBlockWord D a).Nodup)
    [∀ x : D.Slice a, (leftFactor T (V x.val)).LaxBraided]
    (hl : ∀ x : D.Slice a, SameLeftGather T (V x.val) L) :
    AugHom ℙ (wordAug (selectedMatrixLabels (T:=T) D a) (selectedBlockWord D a) (selectedParentSourceAugCell D a R L J ha δ))
      (wordAug (fun t => T.obj (V' a) (W' a t)) (us' a) (selectedParentTargetAugCell (us':=us') (W':=W') (V':=V') a R L J (δ' a))) where
  native := selectedChildBlockMap D R L a ha hh
  preserves := by
    let A := selectedMatrixLabels (T:=T) D a
    let B := fun t => T.obj (V' a) (W' a t)
    let F := fold 𝒮 Zₐ A
    let s := D.slice a
    let ts := selectedPositions (us':=us') a
    let f := selectedChildAddr D a
    let ww := selectedBlockWord D a
    let t := selectedExchange D a
    let rr := selectedRowExpr D a
    let cc := selectedColumnExpr D a
    let e := selectedColumn_leaves D a
    let g := fun (x : D.Slice a) (y : U) => (x,y)
    let b := selectedFibreAt D a
    let c := fun x => ts.flatMap (b x)
    let p := fun x : D.Slice a => wordNativePartitionOrder (D.child x.val) (D.innerSlice_support x) hh
    let o := rowOrders (fun x => (p x).relabel (g x)) s
    let e' := leafPartitionMatrix_leaves g b s ts
    let r := ((o.seq (castOrder e'.symm)).seq (gridOrder t)).seq (castOrder e)
    let d := fun j : Fin (us' a).length => selectedChildBlockCell D R L a ha (us' a)[j] (List.getElem_mem _)
    let α := selectedParentSourceAugCell D a R L J ha δ
    let β := selectedParentTargetAugCell (us':=us') (W':=W') (V':=V') a R L J (δ' a)
    apply (wordNativeMap_preserving_iff f (selectedChild_support D a) hw hh A B d r α β).mpr
    let M := symmetricCross (C:=C)
    let k := eqToHom (wordTotalPin B (us' a))
    let β' := eqToHom (wordTotalPin (W' a) (us' a)) ≫ δ' a
    let W₀ := fun j : Fin (us' a).length => W' a (us' a)[j]
    let tail := Lin.collect (Lin.left L (V' a)) W₀ ts ≫ T.map (𝟙 (V' a)) β' ≫ J.ρ (V' a)
    let A₀ := fun j : Fin (us' a).length => wordFibre ww f (us' a)[j]
    let x₀ := eqToHom (selectedRow_eval (T:=T) D a)
    let x₁ := eqToHom (selectedColumn_eval (T:=T) D a)
    let z := selectedMatrixCell (T:=T) D a
    let y := selectedColumnPureCell D a R L ha
    have r₀ : AddressOrder.mapSum additiveStructure A r =
        AddressOrder.mapSum additiveStructure A o ≫ eqToHom (congrArg F e'.symm) ≫
          AddressOrder.mapSum additiveStructure A (gridOrder t) ≫ eqToHom (congrArg F e) := by
      change ((AddressOrder.mapSum additiveStructure A o ≫ AddressOrder.mapSum additiveStructure A (castOrder e'.symm)) ≫
        AddressOrder.mapSum additiveStructure A (gridOrder t)) ≫ AddressOrder.mapSum additiveStructure A (castOrder e) = _
      rw [castOrder_map, castOrder_map]
      simp only [Category.assoc]
    have hβ : k ≫ β = tail := by
      change k ≫ eqToHom (wordTotalPin B (us' a)).symm ≫ tail = tail
      have h₀ : k ≫ eqToHom (wordTotalPin B (us' a)).symm = 𝟙 _ := by
        change eqToHom _ ≫ eqToHom _ = _
        rw [eqToHom_trans]
        rfl
      rw [reassoc_of% h₀]
    have hcc : eqToHom (congrArg F e) ≫ rowsChart A A₀ ts ≫ act 𝒮 Zₐ d ts =
        compressGrid A cc ≫ x₁ ≫ act 𝒮 Zₐ y ts := (selectedColumn_chart D a R L ha).symm
    have hex : GridCircuit.eval M A t ≫ x₁ = x₀ ≫ transposeBlock M z ts s :=
      heq_paste (selectedRow_eval (T:=T) D a) (selectedColumn_eval (T:=T) D a) (selectedExchange_eval (T:=T) D a)
    have hR : compressGrid A rr ≫ x₀ =
        eqToHom (congrArg F e') ≫ taggedRaggedRows A g c s ≫
          act 𝒮 Zₐ (fun x => rowsChart (A ∘ g x) (b x) ts) s :=
      leafPartitionMatrix_chart A g b s ts
    have hO : AddressOrder.mapSum additiveStructure A o ≫ taggedRaggedRows A g c s =
        taggedRaggedRows A g (us ∘ Subtype.val) s ≫
          act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (A ∘ g x) (p x)) s :=
      taggedRaggedRows_order A g p s
    have hAct : act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (A ∘ g x) (p x)) s ≫
        act 𝒮 Zₐ (fun x => rowsChart (A ∘ g x) (b x) ts) s =
        act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (A ∘ g x) (p x) ≫
          rowsChart (A ∘ g x) (b x) ts) s :=
      act_seq 𝒮 Zₐ _ _ s
    have hId : eqToHom (congrArg F e'.symm) ≫ eqToHom (congrArg F e') = 𝟙 _ := by
      rw [eqToHom_trans]
      rfl
    change AddressOrder.mapSum additiveStructure A r ≫ rowsChart A A₀ ts ≫ act 𝒮 Zₐ d ts ≫ (k ≫ β) = α
    rw [hβ, r₀]
    simp only [Category.assoc]
    rw [reassoc_of% hcc]
    rw [← Category.assoc (AddressOrder.mapSum additiveStructure A (gridOrder t)), compressGrid_order]
    simp only [Category.assoc]
    rw [reassoc_of% hex, reassoc_of% hR, reassoc_of% hId, reassoc_of% hO, reassoc_of% hAct]
    let X := fun x => AddressOrder.mapSum additiveStructure (A ∘ g x) (p x) ≫ rowsChart (A ∘ g x) (b x) ts
    let ep := fun x : D.Slice a => (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫
      T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val)
    let U := taggedRaggedRows A g (us ∘ Subtype.val) s
    have e := selected_parent_native_augmentation D R L N NL J hp a ha hh hx hl
    dsimp only at e
    let m := childMajorParentGather R L (D.parentVal a) W₀ z s ts
      (fun (x : D.Slice a) (j : Fin (us' a).length) =>
        attachedSliceChildCell D L x (us' a)[j] (List.getElem_mem _)) (D.locOuter a ha)
    have hTail : act 𝒮 Zₐ y ts ≫ tail =
        m ≫ T.map (𝟙 (V' a)) β' ≫ J.ρ (V' a) := by
      change act 𝒮 Zₐ y ts ≫ ((Lin.left L (V' a)).collect W₀ ts ≫ T.map (𝟙 (V' a)) β' ≫ J.ρ (V' a)) =
        (act 𝒮 Zₐ y ts ≫ (Lin.left L (V' a)).collect W₀ ts) ≫ T.map (𝟙 (V' a)) β' ≫ J.ρ (V' a)
      rw [Category.assoc]
    have h := congrArg (fun x => U ≫ act 𝒮 Zₐ X s ≫ transposeBlock M z ts s ≫ x) hTail
    exact h.trans (congrArg (fun x => U ≫ x) e)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq X'] [DecidableEq U'] in
theorem selectedParentTargetAug_raw (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {I : C} (J : UnitCompat R I) (δ : fold 𝒮 Zₐ (W' a) (us' a) ⟶ I) :
    selectedParentTargetAugCell (us':=us') (W':=W') (V':=V') a R L J δ =
      (Lin.left L (V' a)).collect (W' a) (us' a) ≫ T.map (𝟙 (V' a)) δ ≫ J.ρ (V' a) := by
  let A := W' a
  let F := Lin.left L (V' a)
  let H := leftFactor T (V' a)
  let B := fun t => T.obj (V' a) (W' a t)
  let t := us' a
  let s := selectedPositions (us':=us') a
  let f := fun i : Fin t.length => t[i]
  let y := F.collect (A ∘ f) s
  let z := F.collect A t
  let e := wordTotalPin A t
  let d := wordTotalPin B t
  have l : s.map f = t := finRange_get t
  have h₁ (p q : List U') (h : p = q) : HEq (F.collect A p) (F.collect A q) := by cases h; rfl
  have h := (h₁ _ _ l.symm).trans (lin_collect_relabel F A f s)
  have h₀ : z ≫ eqToHom (congrArg F.obj e.symm) = eqToHom d.symm ≫ y :=
    heq_paste d.symm (congrArg F.obj e.symm) h
  have m : eqToHom (congrArg H.obj e.symm) ≫ H.map (eqToHom e ≫ δ) = H.map δ := by
    have hf (u v : C) (e : u = v) : eqToHom (congrArg H.obj e) = H.map (eqToHom e) := by
      cases e
      rw [eqToHom_refl, eqToHom_refl, H.map_id]
    rw [hf _ _ e.symm, ← H.map_comp, ← Category.assoc, eqToHom_trans]
    have j : eqToHom (e.symm.trans e) = 𝟙 _ := rfl
    rw [j, Category.id_comp]
  change eqToHom d.symm ≫ y ≫ H.map (eqToHom e ≫ δ) ≫ J.ρ (V' a) = z ≫ H.map δ ≫ J.ρ (V' a)
  rw [← reassoc_of% h₀, reassoc_of% m]

end Matrix

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
