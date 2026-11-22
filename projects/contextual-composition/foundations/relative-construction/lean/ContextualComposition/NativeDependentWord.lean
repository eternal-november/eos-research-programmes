module
public import ContextualComposition.NativeIndependentSourceChart
@[expose] public section

/-! The actual unary dependent carrier map in the same ordered addressed
presentations used by the two existing raw binary arrows. -/
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

def dependentWord (xs : List X) (us : X → List U) : List (X × U) :=
  xs.flatMap (fun x => (us x).map (fun u => (x,u)))

theorem dependentWord_mem (xs : List X) (us : X → List U) (t : X × U) :
    t ∈ dependentWord xs us ↔ t.1 ∈ xs ∧ t.2 ∈ us t.1 := by
  rcases t with ⟨x,u⟩
  simp only [dependentWord, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,rfl,rfl⟩
    exact ⟨ha,hb⟩
  · rintro ⟨hx,hu⟩
    exact ⟨x,hx,u,hu,rfl,rfl⟩

def dependentLabels (A : X → C) (B : X → U → C) (t : X × U) := T.obj (A t.1) (B t.1 t.2)

def origDepCarrier : X × U → X' × U' := fun p => (D.parent p.1,D.child p.1 p.2)

theorem origDepCarrier_support : ∀ t ∈ dependentWord xs us, origDepCarrier D t ∈ dependentWord xs' us' := by
  intro t ht
  have h := (dependentWord_mem xs us t).mp ht
  exact (dependentWord_mem xs' us' _).mpr ⟨D.parent_mem _ h.1,D.child_mem _ h.1 _ h.2⟩

def dependentExpr (xs : List X) (us : X → List U) : GridExpr (X × U) :=
  GridExpr.over (fun x => GridExpr.over (fun u => .leaf (x,u)) (us x)) xs

theorem dependentExpr_leaves (xs : List X) (us : X → List U) :
    (dependentExpr xs us).leaves = dependentWord xs us := by
  unfold dependentExpr dependentWord
  rw [GridExpr.leaves_over]
  exact congrArg (fun g => xs.flatMap g) (funext fun x => leafWord_pin (fun u => (x,u)) (us x))

set_option backward.isDefEq.respectTransparency false in
theorem origDepCarrier_fibre (t : X' × U') :
    wordFibre (dependentWord xs us) (origDepCarrier D) t =
      dependentWord (parentFibreA xs D.parent t.1) (childFibreA us D.child t.2) := by
  rcases t with ⟨a,b⟩
  simp only [wordFibre, dependentWord, parentFibreA, childFibreA, List.filter_flatMap, List.filter_map,
    flatMap_filter_if]
  congr 1
  funext x
  by_cases h : D.parent x = a
  · simp [origDepCarrier, Function.comp_def, Prod.ext_iff, h]
  · simp [origDepCarrier, Function.comp_def, Prod.ext_iff, h]

theorem dependentExpr_eval (V : X → C) (W : X → U → C) (xs : List X) (us : X → List U) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) V W) (dependentExpr xs us) =
      fold 𝒮 Zₐ (rowSource (S:=𝒮) (T:=T) (Z:=Zₐ) V (indexInput W us)) xs := by
  unfold dependentExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  refine (GridExpr.eval_over _ _ _).trans ?_
  exact (std_fold_map (T.obj (V x)) (W x) (us x)).symm

def dependentSliceRelabel (j : X') (p : D.Slice j × U) : X × U := (p.1.val,p.2)

theorem dependentWord_relabel {X₀ : Type u} (f : X₀ → X) (xs : List X₀) (us : X → List U) :
    (dependentWord xs (us ∘ f)).map (fun p => (f p.1,p.2)) =
      dependentWord (xs.map f) us := by
  unfold dependentWord
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext x
  rw [List.map_map]
  rfl

theorem dependentSlice_word (t : X' × U') :
    ((dependentExpr (D.slice t.1) (D.terms t.1 t.2)).leaves).map (dependentSliceRelabel D t.1) =
      wordFibre (dependentWord xs us) (origDepCarrier D) t := by
  rw [dependentExpr_leaves, origDepCarrier_fibre]
  change (dependentWord (D.slice t.1) (childFibreA us D.child t.2 ∘ Subtype.val)).map
    (fun p => (p.1.val,p.2)) = _
  rw [dependentWord_relabel, sliceWord_map]

set_option backward.isDefEq.respectTransparency false in
def origDependentCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (t : X' × U') (ht : t ∈ dependentWord xs' us') :
    fold 𝒮 Zₐ (dependentLabels (T:=T) V W) (wordFibre (dependentWord xs us) (origDepCarrier D) t) ⟶
      dependentLabels (T:=T) V' W' t :=
  let h := (dependentWord_mem xs' us' t).mp ht
  let E := dependentExpr (D.slice t.1) (D.terms t.1 t.2)
  let A := dependentLabels (T:=T) V W
  localCellToGlobal A (dependentSliceRelabel D t.1) (dependentSlice_word D t)
    (compressGrid (fun p => A (dependentSliceRelabel D t.1 p)) E ≫
      eqToHom (dependentExpr_eval (T:=T) (D.parentVal t.1) (D.childVal t.1) (D.slice t.1) (D.terms t.1 t.2)) ≫
      dep R (D.parentVal t.1) (indexInput (D.childVal t.1) (D.terms t.1 t.2)) L
        (D.slice t.1) (D.locInner t.1 t.2 h.2) (D.locOuter t.1 h.1))

noncomputable def origDependentWordMap (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (hn : (dependentWord xs' us').Nodup) :
    Hom ℙ (wordFamily (dependentLabels (T:=T) V W) (dependentWord xs us))
      (wordFamily (dependentLabels (T:=T) V' W') (dependentWord xs' us')) :=
  wordNativeMap (origDepCarrier D) (origDepCarrier_support D) hn
    (dependentLabels (T:=T) V W) (dependentLabels (T:=T) V' W')
    (fun i => origDependentCell D R L (dependentWord xs' us')[i] (List.getElem_mem _))

namespace OrderedDependentMap

noncomputable def outerNative (h : xs'.Nodup) :
    Hom ℙ (wordFamily V xs) (wordFamily V' xs') :=
  wordNativeMap D.parent D.parent_mem h V V'
    (fun j => D.outer xs'[j] (List.getElem_mem _))

noncomputable def innerNative (x : X) (hx : x ∈ xs) (h : (us' (D.parent x)).Nodup) :
    Hom ℙ (wordFamily (W x) (us x)) (wordFamily (W' (D.parent x)) (us' (D.parent x))) :=
  wordNativeMap (D.child x) (D.child_mem x hx) h (W x) (W' (D.parent x))
    (fun j => D.inner x hx (us' (D.parent x))[j] (List.getElem_mem _))

/-- In addition to the original opaque ordered cells, independently state
which outer and continuation maps preserve the actual augmentations. -/
structure Preserves {I : C}
    (hn : xs'.Nodup) (hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I)
    (δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (ε' : fold 𝒮 Zₐ V' xs' ⟶ I) : Prop where
  outer : (D.outerNative hn).comp (wordAug V' xs' ε').ε = (wordAug V xs ε).ε
  inner (x : X) (hx : x ∈ xs) :
    (D.innerNative x hx (hk x hx)).comp (wordAug (W' (D.parent x)) (us' (D.parent x)) (δ' (D.parent x))).ε =
      (wordAug (W x) (us x) (δ x)).ε

end OrderedDependentMap

def dependentWordAugCell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {I : C} (J : UnitCompat R I) (xs : List X) (us : X → List U)
    (V : X → C) (W : X → U → C)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput W us) x ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) :
    fold 𝒮 Zₐ (dependentLabels (T:=T) V W) (dependentWord xs us) ⟶ I :=
  eqToHom (congrArg (fold 𝒮 Zₐ (dependentLabels (T:=T) V W)) (dependentExpr_leaves xs us).symm) ≫
    compressGrid (dependentLabels (T:=T) V W) (dependentExpr xs us) ≫
    eqToHom (dependentExpr_eval V W xs us) ≫ augmentation L J V (indexInput W us) xs δ ε

noncomputable def dependentWordAug (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {I : C} (J : UnitCompat R I) (xs : List X) (us : X → List U)
    (V : X → C) (W : X → U → C)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput W us) x ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) : Aug ℙ I :=
  wordAug (dependentLabels (T:=T) V W) (dependentWord xs us)
    (dependentWordAugCell R L J xs us V W δ ε)

namespace OrderedDependentMap

/-- The actual continuation map of a selected source parent, transported
only along the raw carrier witness identifying its target parent. -/
noncomputable def innerNativeAt {a : X'} (x : D.Slice a) (h : (us' a).Nodup) :
    Hom ℙ (wordFamily (W x.val) (us x.val)) (wordFamily (W' a) (us' a)) := by
  rcases x with ⟨x,hx,e⟩
  subst a
  exact D.innerNative x hx h

theorem innerSlice_support {a : X'} (x : D.Slice a) :
    ∀ y ∈ us x.val, D.child x.val y ∈ us' a := by
  intro y hy
  rcases x with ⟨x,hx,e⟩
  subst a
  exact D.child_mem x hx y hy

def innerSliceCell {a : X'} (x : D.Slice a) (t : U') (ht : t ∈ us' a) :
    fold 𝒮 Zₐ (W x.val) (wordFibre (us x.val) (D.child x.val) t) ⟶ W' a t :=
  eqToHom (std_fold_map id (W x.val) (D.terms a t x)).symm ≫ D.locInner a t ht x

set_option backward.isDefEq.respectTransparency false in
theorem innerNativeAt_word {a : X'} (x : D.Slice a) (h : (us' a).Nodup) :
    D.innerNativeAt x h =
      wordNativeMap (D.child x.val) (innerSlice_support D x) h (W x.val) (W' a)
        (fun j => innerSliceCell D x (us' a)[j] (List.getElem_mem _)) := by
  rcases x with ⟨x,hx,e⟩
  subst a
  change wordNativeMap (D.child x) (D.child_mem x hx) h (W x) (W' (D.parent x))
     (fun j => D.inner x hx (us' (D.parent x))[j] (List.getElem_mem _)) = _
  apply congrArg (wordNativeMap (D.child x) (D.child_mem x hx) h (W x) (W' (D.parent x)))
  funext j
  unfold innerSliceCell locInner
  rw [← Category.assoc, eqToHom_trans]
  have g : eqToHom ((std_fold_map id (W x) (D.terms (D.parent x) (us' (D.parent x))[j] ⟨x,hx,rfl⟩)).symm.trans
      (std_fold_map id (W x) (D.terms (D.parent x) (us' (D.parent x))[j] ⟨x,hx,rfl⟩))) = 𝟙 _ := rfl
  rw [g]
  let k := D.inner x hx (us' (D.parent x))[j] (List.getElem_mem _)
  change k = 𝟙 _ ≫ k ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

noncomputable def outerAsAug {I : C} {hn : xs'.Nodup}
    {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (h : D.Preserves hn hk δ δ' ε ε') :
    AugHom ℙ (wordAug V xs ε) (wordAug V' xs' ε') :=
  ⟨D.outerNative hn, h.outer⟩

noncomputable def innerAsAugAt {I : C} {hn : xs'.Nodup}
    {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (h : D.Preserves hn hk δ δ' ε ε') {a : X'} (x : D.Slice a) (h' : (us' a).Nodup) :
    AugHom ℙ (wordAug (W x.val) (us x.val) (δ x.val)) (wordAug (W' a) (us' a) (δ' a)) where
  native := D.innerNativeAt x h'
  preserves := by
    rcases x with ⟨x,hx,e⟩
    subst a
    exact h.inner x hx

noncomputable def sliceWholeContinuation {a : X'} (x : D.Slice a) (h : (us' a).Nodup) :
    fold 𝒮 Zₐ (W x.val) (us x.val) ⟶ fold 𝒮 Zₐ (W' a) (us' a) :=
  let S := wordNativePartitionOrder (D.child x.val) (innerSlice_support D x) h
  let ts := List.finRange (us' a).length
  AddressOrder.mapSum additiveStructure (W x.val) S ≫
    rowsChart (W x.val) (fun j : Fin (us' a).length => wordFibre (us x.val) (D.child x.val) (us' a)[j]) ts ≫
    act 𝒮 Zₐ (fun j : Fin (us' a).length => innerSliceCell D x (us' a)[j] (List.getElem_mem _)) ts ≫
    eqToHom (wordTotalPin (W' a) (us' a))

set_option backward.isDefEq.respectTransparency false in
theorem sliceWholeContinuation_preserves {I : C} {hn : xs'.Nodup}
    {hk : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I}
    {δ' : ∀ a, fold 𝒮 Zₐ (W' a) (us' a) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {ε' : fold 𝒮 Zₐ V' xs' ⟶ I}
    (h : D.Preserves hn hk δ δ' ε ε') {a : X'} (x : D.Slice a)
    (h' : (us' a).Nodup) (hx : (us x.val).Nodup) :
    sliceWholeContinuation D x h' ≫ δ' a = δ x.val := by
  let r := wordNativePartitionOrder (D.child x.val) (innerSlice_support D x) h'
  let q := fun j : Fin (us' a).length => innerSliceCell D x (us' a)[j] (List.getElem_mem _)
  have e : (D.innerNativeAt x h').comp (wordAug (W' a) (us' a) (δ' a)).ε =
      (wordAug (W x.val) (us x.val) (δ x.val)).ε := (D.innerAsAugAt h x h').preserves
  rw [innerNativeAt_word] at e
  have z := (wordNativeMap_preserving_iff (D.child x.val) (innerSlice_support D x) hx h'
    (W x.val) (W' a) q r (δ x.val) (δ' a)).mp e
  simpa only [sliceWholeContinuation, Category.assoc] using z

end OrderedDependentMap

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
