module
public import ContextualComposition.NativeDependentWord
@[expose] public section

/-! The continuation-side row atom of the dependent parent block. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem linear_word_partition (F : C ⥤ C) [F.LaxBraided] {X : Type w} {Y : Type z}
    (A : X → C) (B : Y → C) (L : Y → List X) {xs : List X} (ys : List Y)
    (r : AddressOrder X xs (ys.flatMap L)) (p : ∀ y, fold 𝒮 Zₐ A (L y) ⟶ B y) :
    AddressOrder.mapSum additiveStructure (fun x => F.obj (A x)) r ≫
      rowsChart (fun x => F.obj (A x)) L ys ≫
      act 𝒮 Zₐ (fun y => Lin.collect (linearFunctor F) A (L y) ≫ F.map (p y)) ys ≫
      Lin.collect (linearFunctor F) B ys =
    Lin.collect (linearFunctor F) A xs ≫
      F.map (AddressOrder.mapSum additiveStructure A r ≫ rowsChart A L ys ≫ act 𝒮 Zₐ p ys) := by
  let G := fun x => F.obj (A x)
  let K := fun y => fold 𝒮 Zₐ A (L y)
  let a := fun y => Lin.collect (linearFunctor F) A (L y)
  let b := fun y => F.map (p y)
  let pp := act 𝒮 Zₐ p ys
  let s := rowsChart A L ys
  let q := AddressOrder.mapSum additiveStructure A r
  let r' := AddressOrder.mapSum additiveStructure G r

  have e := (act_seq 𝒮 Zₐ a b ys).symm
  have n : act 𝒮 Zₐ b ys ≫ Lin.collect (linearFunctor F) B ys = Lin.collect (linearFunctor F) K ys ≫ F.map pp := collect_map_naturality F p ys
  have h := collect_rows F A L ys
  have hh := collect_order F A r
  change r' ≫ rowsChart G L ys ≫ act 𝒮 Zₐ (fun y => a y ≫ b y) ys ≫ Lin.collect (linearFunctor F) B ys =
    Lin.collect (linearFunctor F) A xs ≫ F.map (q ≫ s ≫ pp)
  rw [e]
  simp only [Category.assoc]
  rw [n, reassoc_of% h, reassoc_of% hh]
  rw [F.map_comp, F.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem lin_collect_relabel {X : Type w} {Y : Type z}
    (F : Lin (K:=coeff (C:=C)) 𝒮 Zₐ) (A : X → C) (g : Y → X) (ys : List Y) :
    HEq (Lin.collect F A (ys.map g)) (Lin.collect F (A ∘ g) ys) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    let s := std_fold_map (fun x => F.obj (A x)) g ys
    let t := std_fold_map A g ys
    let x := A (g y)
    let of := fold 𝒮 Zₐ A (ys.map g)
    let tgt := fold 𝒮 Zₐ (A ∘ g) ys
    have E (a b : C) (h : a = b) : HEq (F.cons x a) (F.cons x b) := by cases h; rfl
    have m : HEq
        (𝟙 (F.obj x) ⊗ₘ Lin.collect F A (ys.map g))
        (𝟙 (F.obj x) ⊗ₘ Lin.collect F (A ∘ g) ys) :=
      structural_map_heq (S:=𝒮) (K:=coeff (C:=C)) rfl rfl s (congrArg F.obj t) HEq.rfl ih
    simp only [Lin.collect]
    exact structural_seq_heq (K:=coeff (C:=C))
      (congrArg (fun a => F.obj x ⊗ a) s)
      (congrArg (fun a => F.obj x ⊗ F.obj a) t)
      (congrArg (fun a => F.obj (x ⊗ a)) t) m (E of tgt t)

set_option backward.isDefEq.respectTransparency false in
theorem parentMajorChildGather_augment {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    {X : Type w} {Y : Type z} (V : X → C) (W : Y → C) (A : X → Y → C)
    (xs : List X) (ys : List Y) (p : ∀ x y, A x y ⟶ T.obj (V x) (W y))
    {a : C} (α : fold 𝒮 Zₐ V xs ⟶ a) (β : fold 𝒮 Zₐ W ys ⟶ I) :
    parentMajorChildGather R L V W A xs ys p α ≫ (T.map (𝟙 a) β ≫ J.ρ a) =
      act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (p x) ys ≫ (Lin.left L (V x)).collect W ys ≫
        T.map (𝟙 (V x)) β ≫ J.ρ (V x)) xs ≫ α := by
  let K := coeff (C:=C)
  let u := fold 𝒮 Zₐ W ys
  let b := fold 𝒮 Zₐ V xs
  let r := DependentFibre.gather R V u xs
  let r' := DependentFibre.gather R V I xs
  let q := fun x => act 𝒮 Zₐ (p x) ys ≫ (Lin.left L (V x)).collect W ys
  let e := fun x => T.map (𝟙 (V x)) β
  let j := fun x => J.ρ (V x)
  have h : K.seq (T.map α (K.id u)) (T.map (K.id a) β) =
      K.seq (T.map (K.id b) β) (T.map α (K.id I)) := by
    rw [← T.map_seq, ← T.map_seq, K.seq_id, K.id_seq, K.id_seq, K.seq_id]
  have hn : K.seq (T.map α (K.id I)) (J.ρ a) = K.seq (J.ρ b) α := J.natural α
  have ht : K.seq r (T.map (K.id b) β) = K.seq (act 𝒮 Zₐ e xs) r' :=
    gather_nat R V β xs
  have h₀ : K.seq r' (J.ρ b) = act 𝒮 Zₐ j xs := gather_unit J V xs
  change K.seq (K.seq (act 𝒮 Zₐ q xs) (K.seq r (T.map α (K.id u))))
    (K.seq (T.map (K.id a) β) (J.ρ a)) = _
  simp only [K.assoc]
  rw [← K.assoc (T.map α (K.id u)), h, K.assoc, hn, ← K.assoc r, ht, K.assoc,
    ← K.assoc r', h₀]
  rw [← K.assoc (act 𝒮 Zₐ e xs), ← K.assoc (act 𝒮 Zₐ q xs), act_seq, act_seq]
  have H (x : X) : K.seq (q x) (K.seq (e x) (j x)) =
    act 𝒮 Zₐ (p x) ys ≫ (Lin.left L (V x)).collect W ys ≫ T.map (𝟙 (V x)) β ≫ J.ρ (V x) := by
    simp only [q, e, j, Category.assoc, K, coeff]
  exact congrArg (fun z => z ≫ α) (congrArg (fun k => act 𝒮 Zₐ k xs) (funext H))

section Actual
variable {X U X' U' : Type u} [DecidableEq X'] [DecidableEq U']
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)

def attachedSliceChildCell (L : LeftGather 𝒮 T Zₐ) {a : X'} (x : D.Slice a) (t : U') (ht : t ∈ us' a) :
    fold 𝒮 Zₐ (fun y => T.obj (V x.val) (W x.val y)) (wordFibre (us x.val) (D.child x.val) t) ⟶
      T.obj (V x.val) (W' a t) :=
  (Lin.left L (V x.val)).collect (W x.val) (wordFibre (us x.val) (D.child x.val) t) ≫
    T.map (𝟙 (V x.val)) (D.innerSliceCell x t ht)

set_option backward.isDefEq.respectTransparency false in
theorem attachedSliceChildCell_matches (L : LeftGather 𝒮 T Zₐ) {a : X'} (x : D.Slice a)
    (t : U') (ht : t ∈ us' a) :
    eqToHom (std_fold_map (T.obj (V x.val)) (W x.val) (D.terms a t x)) ≫
      attachedSliceChildCell D L x t ht =
    row (D.parentVal a) (indexInput (D.childVal a) (D.terms a t)) L (D.locInner a t ht) x := by
  let a₀ := V x.val
  let F := Lin.left L a₀
  let w := W x.val
  let ys := D.terms a t x
  let ep := std_fold_map (T.obj a₀) w ys
  let ed := std_fold_map id w ys
  let b := D.locInner a t ht x
  let m := attachedSliceChildCell D L x t ht
  have c : Lin.collect F id (ys.map w) ≫ eqToHom (congrArg F.obj ed) =
       eqToHom ep ≫ Lin.collect F w ys := heq_paste ep (congrArg F.obj ed) (lin_collect_relabel F id w ys)
  have k : eqToHom (congrArg F.obj ed) ≫ (T.map (𝟙 a₀) (eqToHom ed.symm ≫ b)) = T.map (𝟙 a₀) b := by
    let G := leftFactor T a₀
    have hf (u v : C) (e : u = v) : eqToHom (congrArg G.obj e) = G.map (eqToHom e) := by
      cases e
      rw [eqToHom_refl, eqToHom_refl, G.map_id]
    change eqToHom (congrArg G.obj ed) ≫ G.map (eqToHom ed.symm ≫ b) = G.map b
    rw [hf _ _ ed, ← G.map_comp, ← Category.assoc, eqToHom_trans]
    have j : eqToHom (ed.trans ed.symm) = 𝟙 _ := rfl
    rw [j, Category.id_comp]
  change eqToHom ep ≫ (Lin.collect F w ys ≫ T.map (𝟙 a₀) (eqToHom ed.symm ≫ b)) = _
  rw [← Category.assoc, ← c, Category.assoc, k]
  unfold row
  change Lin.collect F id (ys.map w) ≫ T.map (𝟙 a₀) b =
    gatherLeft L a₀ (ys.map w) ≫ T.map (𝟙 a₀) b
  rw [collect_left_eq]

set_option backward.isDefEq.respectTransparency false in
/-- One raw parent row, with its actual, independently varying child
carrier. The very same attached child cells preserve the one whole
continuation augmentation, after their actual addressed partition. -/
theorem attached_slice_child_augmentation (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (h : D.Preserves hn hk δ δ' ε ε') {a : X'} (x : D.Slice a)
    (ha : (us' a).Nodup) (hx : (us x.val).Nodup)
    [(leftFactor T (V x.val)).LaxBraided] (hl : SameLeftGather T (V x.val) L) :
    let r := wordNativePartitionOrder (D.child x.val) (D.innerSlice_support x) ha
    let A := fun y => T.obj (V x.val) (W x.val y)
    let ts := List.finRange (us' a).length
    let L' := fun j : Fin (us' a).length => wordFibre (us x.val) (D.child x.val) (us' a)[j]
    let B := fun j : Fin (us' a).length => W' a (us' a)[j]
    AddressOrder.mapSum additiveStructure A r ≫ rowsChart A L' ts ≫
      act 𝒮 Zₐ (fun j : Fin (us' a).length => attachedSliceChildCell D L x (us' a)[j] (List.getElem_mem _)) ts ≫
      (Lin.left L (V x.val)).collect B ts ≫
      T.map (𝟙 (V x.val)) (eqToHom (wordTotalPin (W' a) (us' a)) ≫ δ' a) ≫ J.ρ (V x.val) =
    (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫ T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val) := by
  intro r A ts L' B
  let F := leftFactor T (V x.val)
  let p := fun j : Fin (us' a).length => D.innerSliceCell x (us' a)[j] (List.getElem_mem _)
  let q := AddressOrder.mapSum additiveStructure (W x.val) r ≫ rowsChart (W x.val) L' ts ≫ act 𝒮 Zₐ p ts
  let b := eqToHom (wordTotalPin (W' a) (us' a)) ≫ δ' a
  let e := Lin.collect (linearFunctor F) (W x.val) (us x.val)
  let v := J.ρ (V x.val)
  have h₁ := linear_word_partition F (W x.val) B L' ts r p
  change AddressOrder.mapSum additiveStructure A r ≫ rowsChart A L' ts ≫
    act 𝒮 Zₐ _ ts ≫ (Lin.left L (V x.val)).collect B ts ≫ F.map b ≫ v =
      _ ≫ F.map (δ x.val) ≫ v
  unfold attachedSliceChildCell
  simp only [← leftFactor_sameCollect T (V x.val) L hl]
  have h₂ := congrArg (fun z => z ≫ F.map b ≫ v) h₁
  simp only [Category.assoc] at h₂
  refine h₂.trans ?_
  have m : q ≫ b = δ x.val := by
    have e := D.sliceWholeContinuation_preserves h x ha hx
    simpa only [q, b, OrderedDependentMap.sliceWholeContinuation, Category.assoc] using e
  change e ≫ F.map q ≫ F.map b ≫ v = e ≫ F.map (δ x.val) ≫ v
  rw [← F.map_comp_assoc, m]

theorem dependentExpr_evalRaw (a : X') (t : U') :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun p => dependentLabels (T:=T) V W (dependentSliceRelabel D a p))
      (dependentExpr (D.slice a) (D.terms a t)) =
    fold 𝒮 Zₐ (fun x : D.Slice a => fold 𝒮 Zₐ
      (fun y => T.obj (V x.val) (W x.val y)) (D.terms a t x)) (D.slice a) := by
  unfold dependentExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  exact GridExpr.eval_over _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Literal coefficient of the original native unary arrow, after its exact
raw stable fibre compared with the corresponding chosen child-column
chart. This is not a competing coefficient definition. -/
theorem origDependentCell_column (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (t : X' × U') (ht : t ∈ dependentWord xs' us') :
    let a := t.1
    let b := t.2
    let h := (dependentWord_mem xs' us' t).mp ht
    let A := dependentLabels (T:=T) V W
    let P := dependentExpr (D.slice a) (D.terms a b)
    origDependentCell D R L t ht =
    localCellToGlobal A (dependentSliceRelabel D a) (dependentSlice_word D t)
      (compressGrid (fun p => A (dependentSliceRelabel D a p)) P ≫
        eqToHom (dependentExpr_evalRaw (T:=T) D a b) ≫
        act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x b h.2) (D.slice a) ≫
        DependentFibre.gather R (D.parentVal a) (W' a b) (D.slice a) ≫
        T.map (D.locOuter a h.1) (𝟙 (W' a b))) := by
  intro a b h A P
  let s := D.slice a
  let F := D.parentVal a
  let G := D.childVal a
  let J := indexInput G (D.terms a b)
  let H := fun x : D.Slice a => D.terms a b x
  let α := D.locOuter a h.1
  let β := D.locInner a b h.2
  let M := dependentSliceRelabel D a
  let v := fun x : D.Slice a => eqToHom (std_fold_map (T.obj (V x.val)) (W x.val) (H x))
  let p := fun x : D.Slice a => attachedSliceChildCell D L x b h.2
  let d := DependentFibre.gather R F (W' a b) s
  have e : eqToHom (dependentExpr_eval (T:=T) F G s H) ≫ act 𝒮 Zₐ v s =
      eqToHom (dependentExpr_evalRaw (T:=T) D a b) := by
    rw [std_act_eqToHom, eqToHom_trans]
  have pp : act 𝒮 Zₐ v s ≫ act 𝒮 Zₐ p s =
      act 𝒮 Zₐ (row F J L β) s :=
    (act_seq 𝒮 Zₐ v p s).trans (congrArg (fun m => act 𝒮 Zₐ m s)
      (funext (fun x => attachedSliceChildCell_matches D L x b h.2)))
  unfold origDependentCell
  apply congrArg (localCellToGlobal A M (dependentSlice_word D t))
  change compressGrid (fun p => A (M p)) P ≫ eqToHom (dependentExpr_eval (T:=T) F G s H) ≫
    (act 𝒮 Zₐ (row F J L β) s ≫ d ≫ T.map α (𝟙 (W' a b))) =
    compressGrid (fun p => A (M p)) P ≫ eqToHom (dependentExpr_evalRaw (T:=T) D a b) ≫
      act 𝒮 Zₐ p s ≫ d ≫ T.map α (𝟙 (W' a b))
  rw [← pp]
  simp only [Category.assoc]
  rw [reassoc_of% e]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- The actual selected target-parent coefficient square: independently
regroup every source child's word, pass through its original opaque cell,
then use the very same outer map at all target children. The square ends
at the opaque target parent's coefficient, not at an independently chosen
parent augmentation. -/
theorem selected_parent_native_augmentation
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    {I : C} (J : UnitCompat R I)
    {hn : xs'.Nodup} {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (h : D.Preserves hn hk δ δ' ε ε') (a : X') (ha : a ∈ xs')
    (hh : (us' a).Nodup) (hx : ∀ x : D.Slice a, (us x.val).Nodup)
    [∀ x : D.Slice a, (leftFactor T (V x.val)).LaxBraided]
    (hl : ∀ x : D.Slice a, SameLeftGather T (V x.val) L) :
    let ts := List.finRange (us' a).length
    let s := D.slice a
    let V₀ := D.parentVal a
    let W₀ := fun j : Fin (us' a).length => W' a (us' a)[j]
    let G := fun (x : D.Slice a) (y : U) => T.obj (V x.val) (W x.val y)
    let F := fun (x : D.Slice a) (j : Fin (us' a).length) =>
      wordFibre (us x.val) (D.child x.val) (us' a)[j]
    let A := fun x j => fold 𝒮 Zₐ (G x) (F x j)
    let P := fun (x : D.Slice a) (j : Fin (us' a).length) =>
      attachedSliceChildCell D L x (us' a)[j] (List.getElem_mem _)
    let r := fun x => wordNativePartitionOrder (D.child x.val) (D.innerSlice_support x) hh
    let β := eqToHom (wordTotalPin (W' a) (us' a)) ≫ δ' a
    let α := D.locOuter a ha
    act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (G x) (r x) ≫ rowsChart (G x) (F x) ts) s ≫
      transposeBlock (symmetricCross (C:=C)) A ts s ≫
      childMajorParentGather R L V₀ W₀ A s ts P α ≫
      T.map (𝟙 (V' a)) β ≫ J.ρ (V' a) =
    act 𝒮 Zₐ (fun x => (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫
      T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val)) s ≫ α := by
  intro ts s V₀ W₀ G F A P r β α
  let M := symmetricCross (C:=C)
  let l := fun x => AddressOrder.mapSum additiveStructure (G x) (r x) ≫ rowsChart (G x) (F x) ts
  let K := fun x => act 𝒮 Zₐ (P x) ts ≫ (Lin.left L (V x.val)).collect W₀ ts ≫
    T.map (𝟙 (V x.val)) β ≫ J.ρ (V x.val)
  let E := fun x : D.Slice a => (Lin.left L (V x.val)).collect (W x.val) (us x.val) ≫
    T.map (𝟙 (V x.val)) (δ x.val) ≫ J.ρ (V x.val)
  let b := T.map (𝟙 (V' a)) β ≫ J.ρ (V' a)
  let p := childMajorParentGather R L V₀ W₀ A s ts P α
  let q := parentMajorChildGather R L V₀ W₀ A s ts P α
  have e₁ : transposeBlock M A ts s ≫ p = q :=
    child_parent_regrouping M R L N NL V₀ W₀ A s ts P α
  have e₂ : q ≫ b = act 𝒮 Zₐ K s ≫ α :=
    parentMajorChildGather_augment R L J V₀ W₀ A s ts P α β
  have e₃ (x : D.Slice a) : l x ≫ K x = E x := by
    have H := attached_slice_child_augmentation D R L J h x hh (hx x) (hl x)
    dsimp only at H
    simpa only [l,K,E,Category.assoc] using H
  have e₄ : act 𝒮 Zₐ l s ≫ act 𝒮 Zₐ K s = act 𝒮 Zₐ E s :=
    (act_seq 𝒮 Zₐ l K s).trans (congrArg (fun k => act 𝒮 Zₐ k s) (funext e₃))
  change act 𝒮 Zₐ l s ≫ transposeBlock M A ts s ≫ p ≫ b = act 𝒮 Zₐ E s ≫ α
  rw [reassoc_of% e₁, e₂, ← Category.assoc (act 𝒮 Zₐ l s), e₄]

end Actual

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
