module
public import ContextualComposition.NativeDependentCompositeLinearity
@[expose] public section

/-! Finish the direct route using only native address regrouping and
the independently supplied parent and continuation whole cells. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

section Slices
variable {X Y : Type u} [DecidableEq Y] {xs : List X} (f : X → Y) (y : Y)
theorem mem_sliceWord_all (p : ParentSlice xs f y) : p ∈ sliceWord xs f y := by
  have h : p.val ∈ parentFibreA xs f y :=
    List.mem_filter.mpr ⟨p.property.1,by simp only [p.property.2,decide_true]⟩
  rw [← sliceWord_map xs f y] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have t : q = p := Subtype.ext e
  exact t ▸ hq

theorem sliceWord_nodup (hn : xs.Nodup) : (sliceWord xs f y).Nodup := by
  have K : ((sliceWord xs f y).map Subtype.val).Nodup := by
    rw [sliceWord_map]
    exact hn.filter _
  exact List.Pairwise.of_map Subtype.val (fun _ _ h e => h (congrArg Subtype.val e)) K

end Slices

section Three
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)

def subgroupParent {z : Z} (y : E.Slice z) (x : D.Slice y.val) :
    (D.compose E hn hm hD hE).Slice z :=
  ⟨x.val,x.property.1,(congrArg E.parent x.property.2).trans y.property.2⟩

def directParentGroups {z : Z} (y : E.Slice z) :
    List ((D.compose E hn hm hD hE).Slice z) :=
  (D.slice y.val).map (subgroupParent D E hn hm hD hE y)

set_option backward.isDefEq.respectTransparency false in
theorem directParentGroups_map {z : Z} (y : E.Slice z) :
    (directParentGroups D E hn hm hD hE y).map Subtype.val =
      parentFibreA xs D.parent y.val := by
  unfold directParentGroups
  rw [List.map_map]
  exact sliceWord_map xs D.parent y.val

set_option backward.isDefEq.respectTransparency false in
theorem subgroupParent_mem_iff {z : Z} (y : E.Slice z) (x : (D.compose E hn hm hD hE).Slice z) :
    x ∈ directParentGroups D E hn hm hD hE y ↔ D.parent x.val = y.val := by
  constructor
  · intro e
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp e
    exact p.property.2
  · intro e
    let p : D.Slice y.val := ⟨x.val,x.property.1,e⟩
    exact List.mem_map.mpr ⟨p,mem_sliceWord_all D.parent y.val p,Subtype.ext rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem directParentGrouping_perm (hx : xs.Nodup) (z : Z) :
    ((D.compose E hn hm hD hE).slice z).Perm
      ((E.slice z).flatMap (directParentGroups D E hn hm hD hE)) := by
  let DC := D.compose E hn hm hD hE
  let I := E.Slice z
  let Q := directParentGroups D E hn hm hD hE (z:=z)
  have h (y : I) : (Q y).Nodup := by
    have k : ((Q y).map Subtype.val).Nodup := by
      rw [directParentGroups_map D E hn hm hD hE y]
      exact hx.filter _
    exact List.Pairwise.of_map Subtype.val (fun _ _ h e => h (congrArg Subtype.val e)) k
  have q (is : List I) (hh : is.Nodup) : (is.flatMap Q).Nodup := by
    induction is with
    | nil => exact List.nodup_nil
    | cons y is ih =>
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨h y,ih (List.nodup_cons.mp hh).2,?_⟩
      intro x hx _ hxy e
      subst e
      obtain ⟨y',hy',h₁⟩ := List.mem_flatMap.mp hxy
      have k := (subgroupParent_mem_iff D E hn hm hD hE y x).mp hx
      have k' := (subgroupParent_mem_iff D E hn hm hD hE y' x).mp h₁
      have v : y = y' := Subtype.ext (k.symm.trans k')
      exact (List.nodup_cons.mp hh).1 (v ▸ hy')
  apply (List.perm_ext_iff_of_nodup (sliceWord_nodup DC.parent z hx) (q (E.slice z) (sliceWord_nodup E.parent z hn))).mpr
  intro x
  refine ⟨fun _ => ?_,fun _ => mem_sliceWord_all DC.parent z x⟩
  let y : I := ⟨D.parent x.val,D.parent_mem _ x.property.1,x.property.2⟩
  exact List.mem_flatMap.mpr ⟨y,mem_sliceWord_all E.parent z y,(subgroupParent_mem_iff D E hn hm hD hE y x).mpr rfl⟩

noncomputable def directParentGrouping (hx : xs.Nodup) (z : Z) :
    AddressOrder ((D.compose E hn hm hD hE).Slice z) ((D.compose E hn hm hD hE).slice z)
      ((E.slice z).flatMap (directParentGroups D E hn hm hD hE)) :=
  Classical.choice (AddressOrder.ofPerm (directParentGrouping_perm D E hn hm hD hE hx z))

end Three

section DirectRawRows
variable {X U Y V : Type u} [DecidableEq Y] [DecidableEq V]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
theorem firstChildGrid_flatCell (y : Y) (x : D.Slice y) (v : IntermediateChild (vs:=vs) y) :
    let G := dependentLabels (T:=T) A B
    let f := fun u => (x.val,u)
    let s := D.terms y v.val x
    let p := leafWord_pin f s
    compressGrid G (firstChildGrid D y x v) ≫ firstChildGrid_cell D L y x v =
      eqToHom (congrArg (fold 𝒮 Zₐ G) p) ≫ eqToHom (std_fold_map G f s) ≫
        attachedSliceChildCell D L x v.val v.property := by
  intro G f s p
  let e := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G (fun u => GridExpr.leaf (f u)) s
  let d := std_fold_map (T.obj (A x.val)) (B x.val) s
  let W := fun u => T.obj (A x.val) (B x.val u)
  have H := compressGrid_leafWord G f s
  have k := attachedSliceChildCell_matches D L x v.val v.property
  change compressGrid G (GridExpr.over (fun u => GridExpr.leaf (f u)) s) ≫ (eqToHom (e.trans d.symm) ≫ _) = _
  rw [← eqToHom_trans e d.symm]
  simp only [Category.assoc]
  rw [reassoc_of% H, ← eqToHom_trans (congrArg (fold 𝒮 Zₐ G) p) (std_fold_map G f s)]
  rw [← k]
  have j : eqToHom d.symm ≫ eqToHom d = 𝟙 _ := by rw [eqToHom_trans]; rfl
  rw [reassoc_of% j]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem origDependentCell_flatRows (t : Y × V) (ht : t ∈ dependentWord ys vs) :
    let G := dependentLabels (T:=T) A B
    let s := D.slice t.1
    let M := D.terms t.1 t.2
    let f := fun (x : D.Slice t.1) u => (x.val,u)
    let K := (dependentWord_mem ys vs t).mp ht
    let e : s.flatMap (fun x => (M x).map (f x)) = wordFibre (dependentWord xs us) (origDepCarrier D) t :=
      by
        have h := dependentSlice_word_raw D t
        unfold dependentWord at h
        rw [List.map_flatMap] at h
        simp only [List.map_map] at h
        exact h
    origDependentCell D R L t ht =
      eqToHom (congrArg (fold 𝒮 Zₐ G) e.symm) ≫
        taggedRaggedRows G f M s ≫ act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x t.2 K.2) s ≫
        DependentFibre.gather R (D.parentVal t.1) (B' t.1 t.2) s ≫
        T.map (D.locOuter t.1 K.1) (𝟙 _) := by
  intro G s M f K e
  let w : IntermediateChild (vs:=vs) t.1 := ⟨t.2,K.2⟩
  let P := fun x => firstChildGrid D t.1 x w
  let Q := fun x => (P x).leaves
  let p := fun x => firstChildGrid_cell D L t.1 x w
  let p' := fun x => attachedSliceChildCell D L x t.2 K.2
  let m := fun x => leafWord_pin (f x) (M x)
  let n := congrArg (fun F => s.flatMap F) (funext m)
  let F := fold 𝒮 Zₐ G
  let E := dependentFibreRawTree D t
  let E' := GridExpr.over P s
  have j : E = E' := by
    cases t with
    | mk a b => exact firstChildGrid_fibre D a w
  let ev := GridExpr.eval (S:=𝒮) (Z:=Zₐ) G
  let j' := congrArg ev j
  have h : compressGrid G E ≫ eqToHom j' =
      eqToHom (congrArg (fun t => F t.leaves) j) ≫ compressGrid G E' := by
    have hh {e₁ e₂ : GridExpr (X × U)} (w : e₁ = e₂) :
      compressGrid G e₁ ≫ eqToHom (congrArg ev w) =
        eqToHom (congrArg (fun u => F u.leaves) w) ≫ compressGrid G e₂ := by
      cases w
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact hh j
  have k := dependentFibreRawCell_assemble D R L t ht
  have k' := firstCell_grouped D R L t.1 K.1 w
  dsimp only at k k'
  change dependentFibreRawCell D R L t ht = eqToHom (j'.trans (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P s)) ≫
    act 𝒮 Zₐ p s ≫ DependentFibre.gather R (D.parentVal t.1) (B' t.1 t.2) s ≫ T.map (D.locOuter t.1 K.1) (𝟙 _) at k'
  rw [← k, k', ← eqToHom_trans j' (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P s)]
  simp only [Category.assoc]
  change eqToHom (congrArg F (dependentFibreRawTree_leaves D t).symm) ≫ compressGrid G E ≫ eqToHom j' ≫ _ = _
  rw [reassoc_of% h, reassoc_of% compressGrid_over]
  let q := fun x => compressGrid G (P x)
  let z := fun x => eqToHom (congrArg F (m x))
  let d := fun x => eqToHom (std_fold_map G (f x) (M x))
  have act_c {A B D : D.Slice t.1 → C} (a : ∀ i, A i ⟶ B i) (b : ∀ i, B i ⟶ D i) :
      act 𝒮 Zₐ a s ≫ act 𝒮 Zₐ b s = act 𝒮 Zₐ (fun x => a x ≫ b x) s := act_seq (S:=𝒮) (Z:=Zₐ) a b s
  rw [reassoc_of% act_c q p]
  have ee : (fun i => q i ≫ p i) = (fun i => z i ≫ d i ≫ p' i) :=
    funext fun x => firstChildGrid_flatCell D L t.1 x w
  rw [ee, ← reassoc_of% act_c, ← reassoc_of% act_c]
  have W : rowsChart G Q s ≫ act 𝒮 Zₐ z s =
    eqToHom (congrArg F n) ≫ rowsChart G (fun x => (M x).map (f x)) s :=
    rowsChart_rows_congr G m s
  rw [reassoc_of% W]
  unfold taggedRaggedRows
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

end DirectRawRows

section Chamber
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
theorem directAttachedChildRow
    (z : Z) (w : W) (hw : w ∈ ws z) (y : E.Slice z) (x : D.Slice y.val) (hx : (us x.val).Nodup)
    [(leftFactor T (A x.val)).LaxBraided] (_hL : SameLeftGather T (A x.val) L)
    (r : AddressOrder U ((D.compose E hn hm hD hE).terms z w (subgroupParent D E hn hm hD hE y x))
      ((intermediateChildRow E (z,w) y).flatMap (fun v => D.terms y.val v.val x))) :
    let s := intermediateChildRow E (z,w) y
    let G := fun u => T.obj (A x.val) (B x.val u)
    let Q := fun (v : IntermediateChild (vs:=vs) y.val) => D.terms y.val v.val x
    let F := Lin.left L (A x.val)
    attachedSliceChildCell (D.compose E hn hm hD hE) L (subgroupParent D E hn hm hD hE y x) w hw =
      AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q s ≫
        act 𝒮 Zₐ (fun v => attachedSliceChildCell D L x v.val v.property) s ≫
        F.collect (fun v => B' y.val v.val) s ≫
        T.map (𝟙 (A x.val)) (secondChildCell E (z,w) hw y) := by
  rcases y with ⟨y,hy,e⟩
  change E.parent y = z at e
  subst z
  rcases x with ⟨x,hx',e⟩
  change D.parent x = y at e
  subst y
  obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp hw
  subst w
  let j : Fin (ws (E.parent (D.parent x))).length := ⟨k,hk⟩
  have H := directChildRow_position D E L hn hm hD hE x hx' hx _hL j r
  dsimp only at H
  let G := fun u => T.obj (A x) (B x u)
  let Q := childFibreA us (fun x => E.child (D.parent x) ∘ D.child x) (ws (E.parent (D.parent x)))[j] x
  let z := E.parent (D.parent x)
  let w := (ws z)[j]
  let C := D.compose E hn hm hD hE
  let xx : C.Slice z := ⟨x,hx',rfl⟩
  let p := C.inner x hx' w (List.getElem_mem _)
  change (Lin.left L (A x)).collect (B x) Q ≫ T.map (𝟙 (A x)) (C.innerSliceCell xx w (List.getElem_mem _)) = _
  have q : C.innerSliceCell xx w (List.getElem_mem _) = p := by
    unfold OrderedDependentMap.innerSliceCell OrderedDependentMap.locInner
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  rw [q]
  exact H

end Chamber

set_option backward.isDefEq.respectTransparency false in
theorem gather_parent_retag {X : Type w} {Y : Type z} {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (A : Y → C) (f : X → Y) (xs : List X) {ys : List Y} (e : xs.map f = ys)
    {a b : C} (p : fold 𝒮 Zₐ A ys ⟶ a) :
    let J := fun y => T.obj (A y) b
    let t := (std_fold_map A f xs).symm.trans (congrArg (fold 𝒮 Zₐ A) e)
    let s := (std_fold_map J f xs).symm.trans (congrArg (fold 𝒮 Zₐ J) e)
    DependentFibre.gather R (A ∘ f) b xs ≫ T.map (eqToHom t ≫ p) (𝟙 b) =
      eqToHom s ≫ DependentFibre.gather R A b ys ≫ T.map p (𝟙 b) := by
  intro J t s
  have h : HEq (DependentFibre.gather R (A ∘ f) b xs) (DependentFibre.gather R A b ys) := by
    subst ys
    exact rightGather_map_heq R A rfl f xs
  let tt := congrArg (fun a => T.obj a b) t
  have e : DependentFibre.gather R (A ∘ f) b xs ≫ eqToHom tt =
      eqToHom s ≫ DependentFibre.gather R A b ys := heq_paste s tt h
  have j : T.map (eqToHom t) (𝟙 b) = eqToHom tt := by
    have Q {x y : C} (e : x = y) :
        T.map (eqToHom e) (𝟙 b) = eqToHom (congrArg (fun a => T.obj a b) e) := by
      cases e
      exact T.map_id _ _
    exact Q t
  have k := bi_map_comp (T:=T) (eqToHom t) p (𝟙 b) (𝟙 b)
  rw [Category.id_comp, j] at k
  rw [← k, reassoc_of% e]


section ParentAssembly
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
theorem directParentGroups_gather
    (hxs : xs.Nodup) (z : Z) (hz : z ∈ zs)
    (b : C) [(rightFactor (T:=T) b).LaxBraided] (_hr : SameRightGather R b) :
    let DC := D.compose E hn hm hD hE
    let s := DC.slice z
    let is := E.slice z
    let V := DC.parentVal z
    let G := fun x => T.obj (V x) b
    let Q := directParentGroups D E hn hm hD hE (z:=z)
    let r := directParentGrouping D E hn hm hD hE hxs z
    let p := fun y : E.Slice z =>
      eqToHom (std_fold_map G (subgroupParent D E hn hm hD hE y) (D.slice y.val)) ≫
      DependentFibre.gather R (D.parentVal y.val) b (D.slice y.val) ≫ T.map (D.locOuter y.val y.property.1) (𝟙 b)
    DependentFibre.gather R V b s ≫ T.map (DC.locOuter z hz) (𝟙 b) =
      AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q is ≫ act 𝒮 Zₐ p is ≫
        DependentFibre.gather R (E.parentVal z) b is ≫ T.map (E.locOuter z hz) (𝟙 b) := by
  obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp hz
  subst z
  intro DC s is V G Q r p
  let j : Fin zs.length := ⟨k,hk⟩
  let z := zs[j]
  let f : DC.Slice z → X := Subtype.val
  let H := fun x => T.obj (A x) b
  let M := fun y : E.Slice z => parentFibreA xs D.parent y.val
  let sf := sliceWord_map xs DC.parent z
  let df := fun y : E.Slice z => directParentGroups_map D E hn hm hD hE y
  let dp : (is.flatMap Q).map f = is.flatMap M :=
    (List.map_flatMap (f:=f) (g:=Q) (l:=is)).trans (congrArg (fun u => is.flatMap u) (funext df))
  let rp := (castOrder sf.symm).seq ((r.relabel f).seq (castOrder dp))
  let q := fun y : E.Slice z => DependentFibre.gather R A b (M y) ≫ T.map (D.outer y.val y.property.1) (𝟙 b)
  let t := DependentFibre.gather R (E.parentVal z) b is ≫ T.map (E.locOuter z (List.getElem_mem _)) (𝟙 b)
  let pf : fold 𝒮 Zₐ G s = fold 𝒮 Zₐ H (parentFibreA xs DC.parent z) :=
    (std_fold_map H f s).symm.trans (congrArg (fold 𝒮 Zₐ H) sf)
  have L := gather_parent_retag R A f s sf (b:=b) (DC.outer z (List.getElem_mem _))
  dsimp only at L
  change DependentFibre.gather R V b s ≫ T.map (DC.locOuter z (List.getElem_mem _)) (𝟙 b) =
    eqToHom pf ≫ DependentFibre.gather R A b (parentFibreA xs DC.parent z) ≫ T.map (DC.outer z (List.getElem_mem _)) (𝟙 b) at L
  change DependentFibre.gather R V b s ≫ T.map (DC.locOuter z (List.getElem_mem _)) (𝟙 b) =
    AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q is ≫ act 𝒮 Zₐ p is ≫ t
  rw [L]
  have K := directParentRows_position D E R hxs hn hm hD hE b _hr j rp
  dsimp only at K
  change DependentFibre.gather R A b (parentFibreA xs DC.parent z) ≫ T.map (DC.outer z (List.getElem_mem _)) (𝟙 b) = AddressOrder.mapSum additiveStructure H rp ≫ rowsChart H M is ≫ act 𝒮 Zₐ q is ≫ t at K
  rw [K]
  have rel := wordChart_retag H (fun y : E.Slice z => T.obj (A' y.val) b) f s Q M is df r q
  dsimp only at rel
  let W := fun y : E.Slice z =>
    eqToHom ((std_fold_map H f (Q y)).symm.trans (congrArg (fold 𝒮 Zₐ H) (df y))) ≫ q y
  have h : AddressOrder.mapSum additiveStructure H rp =
      eqToHom (congrArg (fold 𝒮 Zₐ H) sf.symm) ≫
        AddressOrder.mapSum additiveStructure H ((r.relabel f).seq (castOrder dp)) := by
    change AddressOrder.mapSum additiveStructure H (castOrder sf.symm) ≫ _ = _
    rw [castOrder_map]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc]
  have t0 : eqToHom (pf.trans (congrArg (fold 𝒮 Zₐ H) sf.symm)) =
      eqToHom (std_fold_map H f s).symm := rfl
  rw [t0, ← reassoc_of% rel]
  have equal (y : E.Slice z) : W y = p y := by
    let x := D.slice y.val
    let u : D.Slice y.val → X := Subtype.val
    let e := sliceWord_map xs D.parent y.val
    let e₁ := std_fold_map G (subgroupParent D E hn hm hD hE y) x
    let P := D.outer y.val y.property.1
    have HR := gather_parent_retag R A u x e (b:=b) P
    dsimp only at HR
    change DependentFibre.gather R (D.parentVal y.val) b x ≫ T.map (D.locOuter y.val y.property.1) (𝟙 b) =
        eqToHom ((std_fold_map H u x).symm.trans (congrArg (fold 𝒮 Zₐ H) e)) ≫ q y at HR
    change W y = eqToHom e₁ ≫ DependentFibre.gather R (D.parentVal y.val) b x ≫ T.map (D.locOuter y.val y.property.1) (𝟙 b)
    rw [HR, reassoc_of% eqToHom_trans]
  change AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q is ≫ act 𝒮 Zₐ W is ≫ t = _
  rw [show W = p from funext equal]

end ParentAssembly

set_option backward.isDefEq.respectTransparency false in
theorem rawFibre_partition_perm {X Y Z K : Type u} [DecidableEq Y] [DecidableEq Z]
    {xs : List X} {ys : List Y} {zs : List Z}
    (f : X → Y) (g : Y → Z) (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hy : ys.Nodup) (hz : zs.Nodup) (j : Fin zs.length)
    (is : List K) (q : K → Fin ys.length)
    (e : is.map q = fibreList (wordCarrier g hg hz) j) :
    (wordFibre xs (g ∘ f) zs[j]).Perm
      (is.flatMap (fun i => wordFibre xs f ys[q i])) := by
  let p := wordCarrier f hf hy
  let r := wordCarrier g hg hz
  let a := fun i : Fin xs.length => xs[i]
  let h := wordCarrier_comp f g hf hg hy hz
  let e₁ : (fibreList (r ∘ p) j).map a = wordFibre xs (g ∘ f) zs[j] :=
    (congrArg (fun u => (fibreList u j).map a) h).trans
      (wordCarrier_fibre (g ∘ f) (fun x hx => hg _ (hf x hx)) hz j)
  let e₂ : ((fibreList r j).flatMap (fibreList p)).map a =
      is.flatMap (fun i => wordFibre xs f ys[q i]) := by
    rw [List.map_flatMap, ← e, List.flatMap_map]
    exact congrArg (fun F => is.flatMap F)
      (funext fun i => wordCarrier_fibre f hf hy (q i))
  have s := (rowPartition_perm p r j).map a
  rw [e₁,e₂] at s
  exact s

section ChildOrder
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)

set_option backward.isDefEq.respectTransparency false in
theorem directChildGrouping_perm (z : Z) (w : W) (hw : w ∈ ws z)
    (y : E.Slice z) (x : D.Slice y.val) :
    ((D.compose E hn hm hD hE).terms z w (subgroupParent D E hn hm hD hE y x)).Perm
      ((intermediateChildRow E (z,w) y).flatMap (fun v => D.terms y.val v.val x)) := by
  rcases y with ⟨y,hy,e⟩
  change E.parent y = z at e
  subst z
  rcases x with ⟨x,hx,e⟩
  change D.parent x = y at e
  subst y
  obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp hw
  subst w
  let j : Fin (ws (E.parent (D.parent x))).length := ⟨k,hk⟩
  let y := D.parent x
  let h := D.parent_mem x hx
  let t := (E.parent y,(ws (E.parent y))[j])
  let yy : E.Slice t.1 := ⟨y,h,rfl⟩
  let q := localContinuationIndex (hD x hx)
  let id := intermediateChildRow E t yy
  have ff := localIntermediateChildRow_index E y h (hD x hx) (hE y h) j
  have H := rawFibre_partition_perm (D.child x) (E.child y) (D.child_mem x hx) (E.child_mem y h)
    (hD x hx) (hE y h) j id q ff
  have j : id.flatMap (fun i => childFibreA us D.child (vs y)[q i] x) =
      id.flatMap (fun i => childFibreA us D.child i.val x) :=
    congrArg (fun f => id.flatMap f) (funext fun i =>
      congrArg (fun t => childFibreA us D.child t x) (localContinuationIndex_read (hD x hx) i))
  change List.Perm _ (id.flatMap (fun i => childFibreA us D.child (vs y)[q i] x)) at H
  rw [j] at H
  exact H

noncomputable def directChildGrouping (z : Z) (w : W) (hw : w ∈ ws z)
    (y : E.Slice z) (x : D.Slice y.val) :
    AddressOrder U ((D.compose E hn hm hD hE).terms z w (subgroupParent D E hn hm hD hE y x))
      ((intermediateChildRow E (z,w) y).flatMap (fun v => D.terms y.val v.val x)) :=
  Classical.choice (AddressOrder.ofPerm (directChildGrouping_perm D E hn hm hD hE z w hw y x))

end ChildOrder

section LocalAssembly
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
theorem firstChildGrid_cell_raw_heq (y : Y) (x : D.Slice y) (v : IntermediateChild (vs:=vs) y) :
    HEq (firstChildGrid_cell D L y x v) (attachedSliceChildCell D L x v.val v.property) := by
  have H := attachedSliceChildCell_matches D L x v.val v.property
  unfold firstChildGrid_cell
  exact (hom_source_pin_heq _ _).trans ((heq_of_eq H.symm).trans (hom_source_pin_heq _ _))

set_option backward.isDefEq.respectTransparency false in
theorem groupedFirstSourceCell_raw_matrix (t : Z × W) (hw : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    let G := dependentLabels (T:=T) A B
    let s := D.slice y.val
    let js := intermediateChildRow E t y
    let f := fun (x : D.Slice y.val) u => (x.val,u)
    let M := fun x (v : IntermediateChild (vs:=vs) y.val) => D.terms y.val v.val x
    let p := fun x => act 𝒮 Zₐ (fun v => attachedSliceChildCell D L x v.val v.property) js ≫
      (Lin.left L (D.parentVal y.val x)).collect (fun v => B' y.val v.val) js ≫
      T.map (𝟙 (D.parentVal y.val x)) (secondChildCell E t hw y)
    groupedFirstSourceCell D E R L t hw y =
      eqToHom (leafPartitionMatrix_eval G f M s js) ≫ act 𝒮 Zₐ p s ≫
        DependentFibre.gather R (D.parentVal y.val) (B'' t.1 t.2) s := by
  intro G s js f M p
  let P := firstChildGrid D y.val
  let old := fun x => act 𝒮 Zₐ (firstChildGrid_cell D L y.val x) js ≫
    (Lin.left L (D.parentVal y.val x)).collect (fun v => B' y.val v.val) js ≫
    T.map (𝟙 (D.parentVal y.val x)) (secondChildCell E t hw y)
  let z := DependentFibre.gather R (D.parentVal y.val) (B'' t.1 t.2) s
  let ξ := rowMatrix_pin G P s js
  let ξ' := leafPartitionMatrix_eval G f M s js
  let ep (x : D.Slice y.val) (v : IntermediateChild (vs:=vs) y.val) :
      GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (P x v) =
        fold 𝒮 Zₐ (G ∘ f x) (M x v) := GridExpr.eval_over _ _ _
  let d := fun x : D.Slice y.val => congrArg (fun A => fold 𝒮 Zₐ A js) (funext (ep x))
  let p0 := fun x => act 𝒮 Zₐ (firstChildGrid_cell D L y.val x) js
  let q0 := fun x => act 𝒮 Zₐ (fun v : IntermediateChild (vs:=vs) y.val => attachedSliceChildCell D L x v.val v.property) js
  let e0 := fun x => (Lin.left L (D.parentVal y.val x)).collect (fun v => B' y.val v.val) js ≫
    T.map (𝟙 (D.parentVal y.val x)) (secondChildCell E t hw y)
  have a (x : D.Slice y.val) : HEq (p0 x) (q0 x) :=
    actFamily_heq (funext (ep x)) rfl (firstChildGrid_cell_raw_heq D L y.val x) js
  have b (x : D.Slice y.val) : HEq (old x) (p x) :=
    structural_seq_heq (K:=coeff (C:=C)) (d x) rfl rfl (a x) (show HEq (e0 x) (e0 x) from HEq.rfl)
  let e := congrArg (fun A => fold 𝒮 Zₐ A s) (funext d)
  have h := heq_paste e rfl (actFamily_heq (funext d) rfl b s)
  simp only [eqToHom_refl, Category.comp_id] at h
  change eqToHom ξ ≫ act 𝒮 Zₐ old s ≫ z = eqToHom ξ' ≫ act 𝒮 Zₐ p s ≫ z
  rw [reassoc_of% h, reassoc_of% eqToHom_trans]


noncomputable def groupedContinuationOrder (t : Z × W) (hw : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    let f := fun (x : D.Slice y.val) u => (x.val,u)
    let s := D.slice y.val
    let Q := fun x => (D.compose E hn hm hD hE).terms t.1 t.2 (subgroupParent D E hn hm hD hE y x)
    let F := parentMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    AddressOrder (X × U) (s.flatMap (fun x => (Q x).map (f x))) (F y).leaves := by
  intro f s Q F
  let js := intermediateChildRow E t y
  let M := fun x (v : IntermediateChild (vs:=vs) y.val) => D.terms y.val v.val x
  let r := fun x => (directChildGrouping D E hn hm hD hE t.1 t.2 hw y x).relabel (f x)
  exact (rowOrders r s).seq (castOrder (leafPartitionMatrix_leaves f M s js).symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
theorem groupedContinuation_raw
    (t : Z × W) (hw : t.2 ∈ ws t.1) (y : E.Slice t.1)
    (hx : ∀ x ∈ xs, (us x).Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (_hl : ∀ a : C, SameLeftGather T a L) :
    let G := dependentLabels (T:=T) A B
    let f := fun (x : D.Slice y.val) u => (x.val,u)
    let s := D.slice y.val
    let DC := D.compose E hn hm hD hE
    let Q := fun x => DC.terms t.1 t.2 (subgroupParent D E hn hm hD hE y x)
    let p := fun x => attachedSliceChildCell DC L (subgroupParent D E hn hm hD hE y x) t.2 hw
    let F := parentMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    AddressOrder.mapSum additiveStructure G (groupedContinuationOrder D E hn hm hD hE t hw y) ≫
      compressGrid G (F y) ≫ groupedFirstSourceCell D E R L t hw y =
    taggedRaggedRows G f Q s ≫ act 𝒮 Zₐ p s ≫
      DependentFibre.gather R (D.parentVal y.val) (B'' t.1 t.2) s := by
  intro G f s DC Q p F
  let js := intermediateChildRow E t y
  let M := fun x (v : IntermediateChild (vs:=vs) y.val) => D.terms y.val v.val x
  let r := fun x => directChildGrouping D E hn hm hD hE t.1 t.2 hw y x
  let rr := rowOrders (fun x => (r x).relabel (f x)) s
  let S := fun x => js.flatMap (M x)
  let ξ := congrArg (fold 𝒮 Zₐ G) (leafPartitionMatrix_leaves f M s js)
  let A₀ := fun x => G ∘ f x
  let q₀ := fun x => AddressOrder.mapSum additiveStructure (A₀ x) (r x)
  let q₁ := fun x => rowsChart (A₀ x) (M x) js
  let q₂ := fun x => act 𝒮 Zₐ (fun v : IntermediateChild (vs:=vs) y.val =>
    attachedSliceChildCell D L x v.val v.property) js ≫
      (Lin.left L (D.parentVal y.val x)).collect (fun v => B' y.val v.val) js ≫
      T.map (𝟙 (D.parentVal y.val x)) (secondChildCell E t hw y)
  let z := DependentFibre.gather R (D.parentVal y.val) (B'' t.1 t.2) s
  let e0 := groupedContinuationOrder D E hn hm hD hE t hw y
  have g := groupedFirstSourceCell_raw_matrix D E R L t hw y
  dsimp only at g
  change groupedFirstSourceCell D E R L t hw y = eqToHom (leafPartitionMatrix_eval G f M s js) ≫
    act 𝒮 Zₐ q₂ s ≫ z at g
  rw [g]
  have h := leafPartitionMatrix_chart G f M s js
  change compressGrid G (F y) ≫ eqToHom (leafPartitionMatrix_eval G f M s js) =
    eqToHom ξ ≫ taggedRaggedRows G f S s ≫ act 𝒮 Zₐ q₁ s at h
  rw [reassoc_of% h]
  have m : AddressOrder.mapSum additiveStructure G e0 =
      AddressOrder.mapSum additiveStructure G rr ≫ eqToHom ξ.symm := by
    change AddressOrder.mapSum additiveStructure G rr ≫
      AddressOrder.mapSum additiveStructure G (castOrder (leafPartitionMatrix_leaves f M s js).symm) = _
    rw [castOrder_map]
  rw [m]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have u : AddressOrder.mapSum additiveStructure G rr ≫ taggedRaggedRows G f S s =
      taggedRaggedRows G f Q s ≫ act 𝒮 Zₐ q₀ s := taggedRaggedRows_order G f r s
  rw [reassoc_of% u]
  have act_c {A B D : D.Slice y.val → C} (a : ∀ i, A i ⟶ B i) (b : ∀ i, B i ⟶ D i) :
      act 𝒮 Zₐ a s ≫ act 𝒮 Zₐ b s = act 𝒮 Zₐ (fun x => a x ≫ b x) s :=
    act_seq (S:=𝒮) (Z:=Zₐ) a b s
  rw [reassoc_of% act_c q₁ q₂, reassoc_of% act_c q₀]
  have w (x : D.Slice y.val) : q₀ x ≫ q₁ x ≫ q₂ x = p x := by
    let _ : (leftFactor T (A x.val)).LaxBraided := lF _
    have e := directAttachedChildRow D E hn hm hD hE L t.1 t.2 hw y x (hx x.val x.property.1) (_hl _) (r x)
    dsimp only at e
    exact e.symm
  rw [show (fun x => q₀ x ≫ q₁ x ≫ q₂ x) = p from funext w]

end LocalAssembly

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_read_parents {Q U X Y : Type u} (A : Q → C) (B : Y → C)
    (f : Y → U → Q) (L : Y → List U) (u : X → Y) (xs : List X)
    (p : ∀ x, fold 𝒮 Zₐ (A ∘ f x) (L x) ⟶ B x) :
    let M := fun x => (L x).map (f x)
    let e := List.flatMap_map u M xs
    taggedRaggedRows A f L (xs.map u) ≫ act 𝒮 Zₐ p (xs.map u) ≫ eqToHom (std_fold_map B u xs) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫
      taggedRaggedRows A (f ∘ u) (L ∘ u) xs ≫ act 𝒮 Zₐ (fun x => p (u x)) xs := by
  intro M e
  let G := fun x => fold 𝒮 Zₐ A (M x)
  let k := fun x => eqToHom (std_fold_map A (f x) (L x))
  let w := fun x => k x ≫ p x
  have h (s : List Y) : act 𝒮 Zₐ k s ≫ act 𝒮 Zₐ p s = act 𝒮 Zₐ w s :=
    act_seq (S:=𝒮) (Z:=Zₐ) k p s
  have j : act 𝒮 Zₐ (fun x => k (u x)) xs ≫ act 𝒮 Zₐ (fun x => p (u x)) xs =
      act 𝒮 Zₐ (fun x => w (u x)) xs :=
    act_seq (S:=𝒮) (Z:=Zₐ) (fun x => k (u x)) (fun x => p (u x)) xs
  have m := rowsChart_relabel_index A M u xs
  have n := std_act_map G u w xs
  unfold taggedRaggedRows
  simp only [Category.assoc]
  change rowsChart A M (xs.map u) ≫ act 𝒮 Zₐ k (xs.map u) ≫ act 𝒮 Zₐ p (xs.map u) ≫
    eqToHom (std_fold_map B u xs) =
    eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A (M ∘ u) xs ≫
      act 𝒮 Zₐ (fun x => k (u x)) xs ≫ act 𝒮 Zₐ (fun x => p (u x)) xs
  rw [reassoc_of% h (xs.map u), ← n, reassoc_of% m, j]


section FinalDirect
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

theorem direct_fibre_source_word (t : Z × W) :
    let DC := D.compose E hn hm hD hE
    let s := DC.slice t.1
    let Q := fun x : DC.Slice t.1 => (DC.terms t.1 t.2 x).map (fun u => (x.val,u))
    s.flatMap Q = wordFibre (dependentWord xs us) (origDepCarrier DC) t := by
  intro DC s Q
  have h := dependentSlice_word_raw DC t
  unfold dependentWord at h
  rw [List.map_flatMap] at h
  simp only [List.map_map] at h
  exact h

noncomputable def directGroupOrder (t : Z × W) (hw : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    let DC := D.compose E hn hm hD hE
    let M := fun x : DC.Slice t.1 => (DC.terms t.1 t.2 x).map (fun u => (x.val,u))
    let G := directParentGroups D E hn hm hD hE y
    AddressOrder (X × U) (G.flatMap M)
      (parentMajorGroupTree (groupsP D E t) (groupsQ E t)
        (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val) y).leaves := by
  intro DC M G
  let f := subgroupParent D E hn hm hD hE y
  let e := List.flatMap_map f M (D.slice y.val)
  exact (castOrder e).seq (groupedContinuationOrder D E hn hm hD hE t hw y)

noncomputable def directDependentOrder (hxs : xs.Nodup) (t : Z × W) (hw : t.2 ∈ ws t.1) :
    AddressOrder (X × U)
      (wordFibre (dependentWord xs us) (origDepCarrier (D.compose E hn hm hD hE)) t)
      (dependentParentMajorTree D E t).leaves := by
  let DC := D.compose E hn hm hD hE
  let s := DC.slice t.1
  let is := E.slice t.1
  let Q := directParentGroups D E hn hm hD hE (z:=t.1)
  let M := fun x : DC.Slice t.1 => (DC.terms t.1 t.2 x).map (fun u => (x.val,u))
  let P := parentMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
  let a : (is.flatMap Q).flatMap M = is.flatMap (fun y => (Q y).flatMap M) := List.flatMap_assoc
  let b := GridExpr.leaves_over P is
  exact (castOrder (direct_fibre_source_word D E hn hm hD hE t).symm).seq
    ((liftRows M (directParentGrouping D E hn hm hD hE hxs t.1)).seq
      ((castOrder a).seq ((rowOrders (directGroupOrder D E hn hm hD hE t hw) is).seq (castOrder b.symm))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
theorem directDependent_normalized_coefficient
    (hxs : xs.Nodup) (hc : ∀ x ∈ xs, (us x).Nodup)
    (NR : GatherOuterNat R)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (t : Z × W) (ht : t ∈ dependentWord zs ws) :
    let hw := (dependentWord_mem zs ws t).mp ht
    let G := dependentLabels (T:=T) A B
    let is := E.slice t.1
    let b := B'' t.1 t.2
    let V := fun y : E.Slice t.1 => fold 𝒮 Zₐ (D.parentVal y.val) (D.slice y.val)
    let γ := act 𝒮 Zₐ (fun y : E.Slice t.1 => D.locOuter y.val y.property.1) is ≫ E.locOuter t.1 hw.1
    let F := parentMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    origDependentCell (D.compose E hn hm hD hE) R L t ht =
      AddressOrder.mapSum additiveStructure G (directDependentOrder D E hn hm hD hE hxs t hw.2) ≫
      compressGrid G (dependentParentMajorTree D E t) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G F is) ≫
        act 𝒮 Zₐ (groupedFirstSourceCell D E R L t hw.2) is ≫ DependentFibre.gather R V b is ≫
        T.map γ (𝟙 b) := by
  intro hw G is b V γ F
  let DC := D.compose E hn hm hD hE
  let X₀ := DC.Slice t.1
  let s := DC.slice t.1
  let S := fun x : X₀ => DC.terms t.1 t.2 x
  let f := fun x : X₀ => fun (u : U) => (x.val,u)
  let M := fun x => (S x).map (f x)
  let Q := directParentGroups D E hn hm hD hE (z:=t.1)
  let a := direct_fibre_source_word D E hn hm hD hE t
  let ep := directParentGrouping D E hn hm hD hE hxs t.1
  let e := liftRows M ep
  let eo : (is.flatMap Q).flatMap M = is.flatMap (fun y => (Q y).flatMap M) := List.flatMap_assoc
  let B₀ := fun x : X₀ => T.obj (DC.parentVal t.1 x) b
  let p := fun x => attachedSliceChildCell DC L x t.2 hw.2
  let stage := fun y : E.Slice t.1 =>
      eqToHom (std_fold_map B₀ (subgroupParent D E hn hm hD hE y) (D.slice y.val)) ≫
      DependentFibre.gather R (D.parentVal y.val) b (D.slice y.val) ≫ T.map (D.locOuter y.val y.property.1) (𝟙 b)
  let tail := DependentFibre.gather R (E.parentVal t.1) b is ≫ T.map (E.locOuter t.1 hw.1) (𝟙 b)
  let U := fun y : E.Slice t.1 => (Q y).flatMap M
  let g := fun y => groupedFirstSourceCell D E R L t hw.2 y
  let ro := directGroupOrder D E hn hm hD hE t hw.2
  let fr := fun y : E.Slice t.1 => T.map (D.locOuter y.val y.property.1) (𝟙 b)
  let rem := directDependentOrder D E hn hm hD hE hxs t hw.2
  have h0 := origDependentCell_flatRows DC R L t ht
  dsimp only at h0
  change origDependentCell DC R L t ht = eqToHom (congrArg (fold 𝒮 Zₐ G) a.symm) ≫
    taggedRaggedRows G f S s ≫ act 𝒮 Zₐ p s ≫
    DependentFibre.gather R (DC.parentVal t.1) b s ≫ T.map (DC.locOuter t.1 hw.1) (𝟙 b) at h0
  let _ : (rightFactor (T:=T) b).LaxBraided := rF b
  have hp := directParentGroups_gather D E hn hm hD hE R hxs t.1 hw.1 b (_hr b)
  dsimp only at hp
  change DependentFibre.gather R (DC.parentVal t.1) b s ≫ T.map (DC.locOuter t.1 hw.1) (𝟙 b) =
    AddressOrder.mapSum additiveStructure B₀ ep ≫ rowsChart B₀ Q is ≫ act 𝒮 Zₐ stage is ≫ tail at hp
  rw [h0, hp]
  have r0 := taggedRaggedRows_parent_order G B₀ f S ep p
  change taggedRaggedRows G f S s ≫ act 𝒮 Zₐ p s ≫ AddressOrder.mapSum additiveStructure B₀ ep =
    AddressOrder.mapSum additiveStructure G e ≫ taggedRaggedRows G f S (is.flatMap Q) ≫ act 𝒮 Zₐ p (is.flatMap Q) at r0
  rw [reassoc_of% r0]
  have r1 := taggedRaggedRows_parent_groups G B₀ f S is Q p
  dsimp only at r1
  let p₀ := fun y => taggedRaggedRows G f S (Q y) ≫ act 𝒮 Zₐ p (Q y)
  change taggedRaggedRows G f S (is.flatMap Q) ≫ act 𝒮 Zₐ p (is.flatMap Q) ≫ rowsChart B₀ Q is =
    eqToHom (congrArg (fold 𝒮 Zₐ G) eo) ≫ rowsChart G U is ≫ act 𝒮 Zₐ p₀ is at r1
  rw [reassoc_of% r1]
  have act_c {A B D : E.Slice t.1 → C} (p : ∀ i, A i ⟶ B i) (q : ∀ i, B i ⟶ D i) :
    act 𝒮 Zₐ p is ≫ act 𝒮 Zₐ q is = act 𝒮 Zₐ (fun i => p i ≫ q i) is := act_seq (S:=𝒮) (Z:=Zₐ) p q is
  rw [reassoc_of% act_c p₀ stage]
  let x := fun y => AddressOrder.mapSum additiveStructure G (ro y)
  let y := fun y => compressGrid G (F y)
  have group (j : E.Slice t.1) : p₀ j ≫ stage j = x j ≫ y j ≫ g j ≫ fr j := by
    let u := subgroupParent D E hn hm hD hE j
    let s := D.slice j.val
    have h := taggedRaggedRows_read_parents G B₀ f S u s p
    dsimp only at h
    have hh := groupedContinuation_raw D E hn hm hD hE R L t hw.2 j hc _hl
    dsimp only at hh
    unfold p₀ stage x y g fr
    simp only [Category.assoc]
    change taggedRaggedRows G f S (s.map u) ≫ act 𝒮 Zₐ p (s.map u) ≫ eqToHom (std_fold_map B₀ u s) ≫
      DependentFibre.gather R (D.parentVal j.val) b s ≫ T.map (D.locOuter j.val j.property.1) (𝟙 b) = _
    rw [reassoc_of% h]
    have hh' : AddressOrder.mapSum additiveStructure G (groupedContinuationOrder D E hn hm hD hE t hw.2 j) ≫
      compressGrid G (F j) ≫ groupedFirstSourceCell D E R L t hw.2 j =
      taggedRaggedRows G (f ∘ u) (S ∘ u) s ≫ act 𝒮 Zₐ (fun x => p (u x)) s ≫
        DependentFibre.gather R (D.parentVal j.val) b s := hh
    rw [← reassoc_of% hh']
    change eqToHom (congrArg (fold 𝒮 Zₐ G) (List.flatMap_map u M s)) ≫ _ =
      AddressOrder.mapSum additiveStructure G (directGroupOrder D E hn hm hD hE t hw.2 j) ≫ _
    unfold directGroupOrder
    change _ = (AddressOrder.mapSum additiveStructure G (castOrder (List.flatMap_map u M s)) ≫ _) ≫ _
    simp only [castOrder_map, Category.assoc]
  rw [show (fun i => p₀ i ≫ stage i) = (fun i => x i ≫ y i ≫ g i ≫ fr i) from funext group]
  rw [← reassoc_of% act_c x]
  have hT := rowsChart_rowOrders G ro is
  change AddressOrder.mapSum additiveStructure G (rowOrders ro is) ≫
      rowsChart G (fun y => (F y).leaves) is = rowsChart G U is ≫ act 𝒮 Zₐ x is at hT
  rw [← reassoc_of% hT]
  rw [← reassoc_of% act_c y, ← reassoc_of% act_c g]
  have n := gather_outer NR (fun (j : E.Slice t.1) => D.locOuter j.val j.property.1) b is
  change act 𝒮 Zₐ fr is ≫ DependentFibre.gather R (E.parentVal t.1) b is =
      DependentFibre.gather R V b is ≫ T.map (act 𝒮 Zₐ (fun j => D.locOuter j.val j.property.1) is) (𝟙 b) at n
  unfold tail
  rw [reassoc_of% n, bi_map_comp, Category.id_comp]
  have hT' := compressGrid_over G F is
  change _ = AddressOrder.mapSum additiveStructure G rem ≫ compressGrid G (GridExpr.over F is) ≫
    eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G F is) ≫ act 𝒮 Zₐ g is ≫
      DependentFibre.gather R V b is ≫ T.map γ (𝟙 b)
  rw [reassoc_of% hT']
  let ξ := GridExpr.leaves_over F is
  have order_map : AddressOrder.mapSum additiveStructure G rem ≫
    eqToHom (congrArg (fold 𝒮 Zₐ G) ξ) =
    eqToHom (congrArg (fold 𝒮 Zₐ G) a.symm) ≫ AddressOrder.mapSum additiveStructure G e ≫
      eqToHom (congrArg (fold 𝒮 Zₐ G) eo) ≫ AddressOrder.mapSum additiveStructure G (rowOrders ro is) := by
    unfold rem directDependentOrder
    simp only [AddressOrder.mapSum, Category.assoc, castOrder_map, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  rw [reassoc_of% order_map]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3600000 in
/-- Functoriality of the literal ordered unary dependent accumulation.
The direct arrow uses native composition of the opaque parent and each
opaque continuation input. The sequential arrow is the composite of
the independently constructed accumulated outputs. -/
theorem origDependentWordMap_comp
    (hxs : xs.Nodup) (hc : ∀ x ∈ xs, (us x).Nodup)
    (h : (dependentWord ys vs).Nodup) (h' : (dependentWord zs ws).Nodup)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    origDependentWordMap (D.compose E hn hm hD hE) R L h' =
      (origDependentWordMap D R L h).comp (origDependentWordMap E R L h') := by
  let h₀ := dependentWord_nodup hxs hc
  let DC := D.compose E hn hm hD hE
  let zw := dependentWord zs ws
  let G := dependentLabels (T:=T) A B
  let G' := dependentLabels (T:=T) A'' B''
  let f := origDepCarrier E ∘ origDepCarrier D
  let support := fun x hx => origDepCarrier_support E _ (origDepCarrier_support D x hx)
  let edge := (wordCarrier_comp (origDepCarrier D) (origDepCarrier E)
    (origDepCarrier_support D) (origDepCarrier_support E) h h').symm
  let p := (origDependentWordMap D R L h).comp (origDependentWordMap E R L h')
  let q := fun j : Fin zw.length => origDependentCell DC R L zw[j] (List.getElem_mem _)
  let p' := readNativeWordCell G G' f support h' p edge
  have hq (k : Fin zw.length) : q k = p' k := by
    let t := zw[k]
    let ht : t ∈ zw := List.getElem_mem _
    let hw := (dependentWord_mem zs ws t).mp ht
    let r := directDependentOrder D E hn hm hD hE hxs t hw.2
    let s := sequential_group_order D E h h' k
    have d := directDependent_normalized_coefficient D E hn hm hD hE R L hxs hc NR _hl _hr t ht
    have c := sequentialDependent_normalized_coefficient D E R L N NR NL h₀ h h' k
    dsimp only at c d
    have e : AddressOrder.mapSum additiveStructure G r = AddressOrder.mapSum additiveStructure G s :=
      tagged_permutation_coherent G (h₀.filter _) r s
    change q k = AddressOrder.mapSum additiveStructure G r ≫ _ at d
    change p' k = AddressOrder.mapSum additiveStructure G s ≫ _ at c
    rw [e] at d
    exact d.trans c.symm
  change wordNativeMap f support h' G G' q = p
  rw [show q = p' from funext hq]
  exact readNativeWordCell_reassemble G G' f support h' p edge

end FinalDirect

section Augmented
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable {I : C} (J : UnitCompat R I)

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentMap.accumulateAug
    {X U Y V : Type u} [DecidableEq X] [DecidableEq Y] [DecidableEq V]
    {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V}
    {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C}
    (D : OrderedDependentMap xs us ys vs A B A' B')
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (_hl : ∀ a : C, SameLeftGather T a L)
    (hx : xs.Nodup) (hy : ys.Nodup) (hxs : ∀ x ∈ xs, (us x).Nodup) (hys : ∀ y ∈ ys, (vs y).Nodup)
    {α : fold 𝒮 Zₐ A xs ⟶ I} {β : fold 𝒮 Zₐ A' ys ⟶ I}
    {δ : ∀ x, fold 𝒮 Zₐ (B x) (us x) ⟶ I}
    {δ' : ∀ y, fold 𝒮 Zₐ (B' y) (vs y) ⟶ I}
    (_p : D.Preserves hy (fun x hx => hys (D.parent x) (D.parent_mem x hx)) δ δ' α β) :
    AugHom ℙ (dependentWordAug R L J xs us A B (indexedAugmentation δ) α)
      (dependentWordAug R L J ys vs A' B' (indexedAugmentation δ') β) where
  native := origDependentWordMap D R L (dependentWord_nodup hy hys)
  preserves := unaryPreserves_of_orderedInputs D R L J N NL _hl hx hy hxs hys _p

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.accumulateAug_ident
    {X U : Type u} [DecidableEq X] [DecidableEq U]
    (xs : List X) (us : X → List U) (A : X → C) (B : X → U → C)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (hx : xs.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup)
    (α : fold 𝒮 Zₐ A xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (B x) (us x) ⟶ I) :
    accumulateAug R L J (identity xs us A B hx hu) N NL hl hx hx hu hu
      (identity_preserves xs us A B hx hu δ α) =
    AugHom.ident (dependentWordAug R L J xs us A B (indexedAugmentation δ) α) := by
  apply AugHom.ext
  exact origDependentWordMap_ident xs us A B hx hu R L hl _hr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
theorem OrderedDependentMap.accumulateAug_comp
    {X U Y V Z W : Type u} [DecidableEq X] [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
    {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
    {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
    (D : OrderedDependentMap xs us ys vs A B A' B')
    (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
    (N : GridBinary (symmetricCross (C:=C)) R L) (_NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (hxs : xs.Nodup) (hys : ys.Nodup) (hzs : zs.Nodup)
    (hu : ∀ x ∈ xs, (us x).Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup) (hw : ∀ z ∈ zs, (ws z).Nodup)
    {α : fold 𝒮 Zₐ A xs ⟶ I} {β : fold 𝒮 Zₐ A' ys ⟶ I} {γ : fold 𝒮 Zₐ A'' zs ⟶ I}
    {δ : ∀ x, fold 𝒮 Zₐ (B x) (us x) ⟶ I}
    {δ' : ∀ y, fold 𝒮 Zₐ (B' y) (vs y) ⟶ I}
    {δ'' : ∀ z, fold 𝒮 Zₐ (B'' z) (ws z) ⟶ I}
    (p : D.Preserves hys (fun x hx => hv _ (D.parent_mem x hx)) δ δ' α β)
    (q : E.Preserves hzs (fun y hy => hw _ (E.parent_mem y hy)) δ' δ'' β γ) :
    let hd := fun x hx => hv (D.parent x) (D.parent_mem x hx)
    let he := fun y hy => hw (E.parent y) (E.parent_mem y hy)
    accumulateAug R L J (D.compose E hys hzs hd he) N NL hl hxs hzs hu hw
      (D.compose_preserves E hys hzs hd he p q) =
    (accumulateAug R L J D N NL hl hxs hys hu hv p).comp (accumulateAug R L J E N NL hl hys hzs hv hw q) := by
  intro hd he
  apply AugHom.ext
  exact origDependentWordMap_comp D E hys hzs hd he R L hxs hu
    (dependentWord_nodup hys hv) (dependentWord_nodup hzs hw) N _NR NL hl _hr

end Augmented
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
