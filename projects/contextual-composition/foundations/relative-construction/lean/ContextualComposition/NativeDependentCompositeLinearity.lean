module
public import ContextualComposition.NativeSupportedGrid
@[expose] public section

/-! Linearity of the decoded composite cell, without replacing either
of the original whole aggregation maps by leafwise operations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
/-- Gathering the product through a decoded composite is the literal
partition, first-stage gathers and opaque cells, then the second-stage
gather and opaque cell. No restriction on empty intermediate fibres. -/
theorem linear_readCompositeWordCell
    (F : C ⥤ C) [F.LaxBraided]
    {X Y Z : Type u} [DecidableEq Y] [DecidableEq Z]
    {xs : List X} {ys : List Y} {zs : List Z}
    (A : X → C) (B : Y → C) (D : Z → C) (f : X → Y) (g : Y → Z)
    (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hx : xs.Nodup) (hy : ys.Nodup) (hz : zs.Nodup)
    (p : ∀ j : Fin ys.length, fold 𝒮 Zₐ A (wordFibre xs f ys[j]) ⟶ B ys[j])
    (q : ∀ j : Fin zs.length, fold 𝒮 Zₐ B (wordFibre ys g zs[j]) ⟶ D zs[j])
    (k : Fin zs.length)
    (r : AddressOrder X (wordFibre xs (g ∘ f) zs[k])
      ((fibreList (wordCarrier g hg hz) k).flatMap (fun j => wordFibre xs f ys[j]))) :
    let s := wordFibre xs (g ∘ f) zs[k]
    let t := fibreList (wordCarrier g hg hz) k
    let K := linearFunctor F
    let B₀ := fun j : Fin ys.length => B ys[j]
    let Q := fun j : Fin ys.length => wordFibre xs f ys[j]
    let G := fun i => F.obj (A i)
    Lin.collect K A s ≫ F.map (readNativeWordCell A D (g ∘ f) (fun x hx => hg _ (hf x hx)) hz
      ((wordNativeMap f hf hy A B p).comp (wordNativeMap g hg hz B D q))
      (wordCarrier_comp f g hf hg hy hz).symm k) =
      AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q t ≫
        act 𝒮 Zₐ (fun j => Lin.collect K A (Q j) ≫ F.map (p j)) t ≫
        Lin.collect K B₀ t ≫ F.map (eqToHom (wordCarrier_fibre_pin g hg hz B k) ≫ q k) := by
  intro s t K B₀ Q G
  have h := readCompositeWordCell_raw A B D f g hf hg hy hz hx p q k r
  have h' := linear_word_partition F A B₀ Q t r p
  let tail := eqToHom (wordCarrier_fibre_pin g hg hz B k) ≫ q k
  let body := AddressOrder.mapSum additiveStructure A r ≫ rowsChart A Q t ≫ act 𝒮 Zₐ p t
  have k0 : AddressOrder.mapSum additiveStructure A r ≫ rowsChart A Q t ≫ act 𝒮 Zₐ p t ≫ tail =
    body ≫ tail := by simp only [body, Category.assoc]
  rw [h, k0, F.map_comp, ← Category.assoc, ← h']
  simp only [Category.assoc]
  rfl


theorem graftGrid_supportedRetag {X : Type w} {Y : Type z} {Z : Type u}
    (P : X → Prop) (f : {x // P x} → Y) (G : Y → GridExpr Z) (H : X → GridExpr Z)
    (e : GridExpr X) (h : ∀ x ∈ e.leaves, P x) (_eq : ∀ x (hx : P x), G (f ⟨x,hx⟩) = H x) :
    graftGrid G (supportedRetagGrid P f e h) = graftGrid H e := by
  induction e with
  | zero => rfl
  | leaf x => exact _eq x _
  | bin a b ha hb =>
    exact congrArg₂ GridExpr.bin (ha (fun x hx => h x (List.mem_append_left _ hx)))
      (hb (fun x hx => h x (List.mem_append_right _ hx)))

section SequentialShape
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')

theorem sequentialDependentFibreTree_shape (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    sequentialDependentFibreTree D E h t =
      GridExpr.over (fun y => GridExpr.over (fun v => dependentFibreRawTree D (y.val,v))
        (E.terms t.1 t.2 y)) (E.slice t.1) := by
  let s := dependentWord ys vs
  let G := fun j : Fin s.length => dependentFibreRawTree D s[j]
  let H := fun p : E.Slice t.1 × V => dependentFibreRawTree D (dependentSliceRelabel E t.1 p)
  let ie := dependentFibreLocalTree E t
  let P := fun p : E.Slice t.1 × V => dependentSliceRelabel E t.1 p ∈ s
  let f := fun p : {x // P x} =>
    (wordPositions s h).symm ⟨dependentSliceRelabel E t.1 p.val,p.property⟩
  have e (p : E.Slice t.1 × V) (hp : P p) : G (f ⟨p,hp⟩) = H p :=
    congrArg (dependentFibreRawTree D) (congrArg Subtype.val
      ((wordPositions s h).apply_symm_apply ⟨dependentSliceRelabel E t.1 p,hp⟩))
  change graftGrid G (supportedRetagGrid P f ie (dependentFibreLocalSupport E t)) = _
  rw [graftGrid_supportedRetag P f G H ie (dependentFibreLocalSupport E t) e]
  unfold ie dependentFibreLocalTree dependentExpr
  rw [graftGrid_over]
  congr 1
  funext y
  rw [graftGrid_over]
  rfl

end SequentialShape

theorem supportedRetagGrid_over {X : Type w} {Y : Type z} {J : Type u}
    (P : X → Prop) (f : {x // P x} → Y) (g : J → GridExpr X)
    (H : ∀ j, ∀ x ∈ (g j).leaves, P x) (xs : List J)
    (h : ∀ x ∈ (GridExpr.over g xs).leaves, P x) :
    supportedRetagGrid P f (GridExpr.over g xs) h =
      GridExpr.over (fun j => supportedRetagGrid P f (g j) (H j)) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change GridExpr.bin (supportedRetagGrid P f (g a) (H a))
      (supportedRetagGrid P f (GridExpr.over g as) _) = _
    rw [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem supportedRetagGrid_leaf_over {X : Type w} {Y : Type z} {J : Type u}
    (P : X → Prop) (f : {x // P x} → Y) (g : J → X) (xs : List J)
    (h : ∀ x ∈ (GridExpr.over (fun j => .leaf (g j)) xs).leaves, P x)
    (H : ∀ j ∈ xs, P (g j)) :
    supportedRetagGrid P f (GridExpr.over (fun j => .leaf (g j)) xs) h =
      GridExpr.over GridExpr.leaf (xs.pmap (fun j hj => f ⟨g j,hj⟩) H) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change GridExpr.bin (GridExpr.leaf (f ⟨g a, H a List.mem_cons_self⟩))
      (supportedRetagGrid P f (GridExpr.over (fun j => .leaf (g j)) as) _) =
      GridExpr.bin (GridExpr.leaf (f ⟨g a, H a List.mem_cons_self⟩))
        (GridExpr.over GridExpr.leaf
          (as.pmap (fun j hj => f ⟨g j,hj⟩) (fun j hj => H j (List.mem_cons_of_mem _ hj))))
    rw [ih]

section SupportedRows
variable {Y V Z W : Type u} [DecidableEq Z] [DecidableEq W]
variable {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')

theorem secondChildSupport (t : Z × W) (y : E.Slice t.1) (v : V) (hv : v ∈ E.terms t.1 t.2 y) :
    (y.val,v) ∈ dependentWord ys vs := by
  have H : v ∈ vs y.val := (List.mem_filter.mp hv).1
  exact (dependentWord_mem ys vs (y.val,v)).mpr ⟨y.property.1,H⟩

noncomputable def secondChildFinRow (h : (dependentWord ys vs).Nodup) (t : Z × W) (y : E.Slice t.1) :
    List (Fin (dependentWord ys vs).length) :=
  (E.terms t.1 t.2 y).pmap
    (fun v hv => (wordPositions (dependentWord ys vs) h).symm ⟨(y.val,v),hv⟩)
    (secondChildSupport E t y)

theorem secondChildFinRow_read (h : (dependentWord ys vs).Nodup) (t : Z × W) (y : E.Slice t.1) :
    let yw := dependentWord ys vs
    (secondChildFinRow E h t y).map (fun i : Fin yw.length => yw[i]) =
      (E.terms t.1 t.2 y).map (fun v => (y.val,v)) := by
  intro yw
  unfold secondChildFinRow
  rw [List.map_pmap]
  have h₀ (v : V) (hv : (y.val,v) ∈ yw) :
      yw[(wordPositions yw h).symm ⟨(y.val,v),hv⟩] = (y.val,v) :=
    congrArg Subtype.val ((wordPositions yw h).apply_symm_apply ⟨(y.val,v),hv⟩)
  refine (List.pmap_congr_left _ (H₂:=fun _ _ => True.intro) (fun v _ hq (_ : True) => h₀ v hq)).trans ?_
  exact List.pmap_eq_map (fun _ _ => True.intro)

set_option backward.isDefEq.respectTransparency false in
theorem dependentFibreIndexTree_over (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    dependentFibreIndexTree E h t =
      GridExpr.over (fun y => GridExpr.over GridExpr.leaf (secondChildFinRow E h t y)) (E.slice t.1) := by
  let yw := dependentWord ys vs
  let P := fun p : E.Slice t.1 × V => dependentSliceRelabel E t.1 p ∈ yw
  let f := fun p : {x // P x} => (wordPositions yw h).symm ⟨dependentSliceRelabel E t.1 p.val,p.property⟩
  let g := fun y : E.Slice t.1 =>
    GridExpr.over (fun v => GridExpr.leaf (y,v)) (E.terms t.1 t.2 y)
  have H (y : E.Slice t.1) : ∀ p ∈ (g y).leaves, P p := by
    intro p hp
    have h₀ := leafWord_pin (fun v => (y,v)) (E.terms t.1 t.2 y)
    change p ∈ (GridExpr.over (fun v => GridExpr.leaf (y,v)) (E.terms t.1 t.2 y)).leaves at hp
    rw [h₀] at hp
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    exact secondChildSupport E t y v hv
  change supportedRetagGrid P f (GridExpr.over g (E.slice t.1)) _ = _
  rw [supportedRetagGrid_over P f g H]
  apply congrArg (fun K => GridExpr.over K (E.slice t.1))
  funext y
  exact supportedRetagGrid_leaf_over P f (fun v => (y,v)) (E.terms t.1 t.2 y) (H y)
    (secondChildSupport E t y)

end SupportedRows

section ChildComposite
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable {T : Bi (coeff (C:=C))}
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
/-- The actual one-step continuation, with its parent coefficient
attached, is exactly the two-stage continuation partition and the two
opaque continuation cells. This is evaluated at one actual final child. -/
theorem compositeChild_linear_read
    (hn : ys.Nodup) (hm : zs.Nodup)
    (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
    (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
    (x : X) (hx : x ∈ xs) (hxs : (us x).Nodup)
    [(leftFactor T (A x)).LaxBraided] (_hL : SameLeftGather T (A x) L)
    (k : Fin (ws (E.parent (D.parent x))).length)
    (r : AddressOrder U
      (childFibreA us (fun x => E.child (D.parent x) ∘ D.child x) (ws (E.parent (D.parent x)))[k] x)
      ((fibreList (E.innerNative (D.parent x) (D.parent_mem x hx) (hE _ (D.parent_mem x hx))).addr k).flatMap
        (fun j => childFibreA us D.child (vs (D.parent x))[j] x))) :
    let y := D.parent x
    let z := E.parent y
    let t := (ws z)[k]
    let p := fun j : Fin (vs y).length => D.inner x hx (vs y)[j] (List.getElem_mem _)
    let q := E.inner y (D.parent_mem x hx) t (List.getElem_mem _)
    let g := wordCarrier (E.child y) (E.child_mem y (D.parent_mem x hx)) (hE y (D.parent_mem x hx))
    let mid := fibreList g k
    let Q := fun j => childFibreA us D.child (vs y)[j] x
    let G := fun u => T.obj (A x) (B x u)
    let F := Lin.left L (A x)
    F.collect (B x) (childFibreA us (fun x => E.child (D.parent x) ∘ D.child x) t x) ≫
      T.map (𝟙 (A x)) ((D.compose E hn hm hD hE).inner x hx t (List.getElem_mem _)) =
    AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q mid ≫
      act 𝒮 Zₐ (fun j => F.collect (B x) (Q j) ≫ T.map (𝟙 (A x)) (p j)) mid ≫
      F.collect (fun j : Fin (vs y).length => B' y (vs y)[j]) mid ≫
      T.map (𝟙 (A x)) (eqToHom (wordCarrier_fibre_pin (E.child y)
        (E.child_mem y (D.parent_mem x hx)) (hE y (D.parent_mem x hx)) (B' y) k) ≫ q) := by
  intro y z t p q g mid Q G F
  let hxy := D.parent_mem x hx
  let F₀ := leftFactor T (A x)
  let p₀ := D.innerNative x hx (hD x hx)
  let q₀ := E.innerNative y hxy (hE y hxy)
  let hg := wordCarrier_comp (D.child x) (E.child y) (D.child_mem x hx) (E.child_mem y hxy)
    (hD x hx) (hE y hxy)
  have d := decodeNativeWordCell_get (B x) (B'' z) (E.child y ∘ D.child x)
    (fun _ hu => E.child_mem y hxy _ (D.child_mem x hx _ hu)) (hE y hxy) (p₀.comp q₀) hg.symm k
  change (D.compose E hn hm hD hE).inner x hx t (List.getElem_mem _) = _ at d
  rw [d]
  have h := linear_readCompositeWordCell F₀ (B x) (B' y) (B'' z)
    (D.child x) (E.child y) (D.child_mem x hx) (E.child_mem y hxy)
    hxs (hD x hx) (hE y hxy) p (fun j => E.inner y hxy (ws z)[j] (List.getElem_mem _)) k r
  dsimp only at h
  unfold F₀ at h
  simp only [leftFactor_sameCollect T (A x) L _hL] at h
  exact h

end ChildComposite

section ParentComposite
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
/-- For any fixed final continuation coefficient, the one-step opaque
parent composite under its actual right gather expands into both
original parent whole-fibre cells and their exact partition. -/
theorem compositeParent_linear_read
    (hxs : xs.Nodup) (hn : ys.Nodup) (hm : zs.Nodup)
    (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
    (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
    (b : C) [(rightFactor (T:=T) b).LaxBraided] (_hR : SameRightGather R b)
    (k : Fin zs.length)
    (r : AddressOrder X
      (parentFibreA xs (E.parent ∘ D.parent) zs[k])
      ((fibreList (E.outerNative hm).addr k).flatMap (fun j => parentFibreA xs D.parent ys[j]))) :
    let p := fun j : Fin ys.length => D.outer ys[j] (List.getElem_mem _)
    let q := E.outer zs[k] (List.getElem_mem _)
    let g := wordCarrier E.parent E.parent_mem hm
    let mid := fibreList g k
    let Q := fun j : Fin ys.length => parentFibreA xs D.parent ys[j]
    let G := fun x => T.obj (A x) b
    DependentFibre.gather R A b (parentFibreA xs (E.parent ∘ D.parent) zs[k]) ≫
      T.map ((D.compose E hn hm hD hE).outer zs[k] (List.getElem_mem _)) (𝟙 b) =
    AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q mid ≫
      act 𝒮 Zₐ (fun j => DependentFibre.gather R A b (Q j) ≫ T.map (p j) (𝟙 b)) mid ≫
      DependentFibre.gather R (fun j : Fin ys.length => A' ys[j]) b mid ≫
      T.map (eqToHom (wordCarrier_fibre_pin E.parent E.parent_mem hm A' k) ≫ q) (𝟙 b) := by
  intro p q g mid Q G
  let F₀ := rightFactor (T:=T) b
  let p₀ := D.outerNative hn
  let q₀ := E.outerNative hm
  let hC := (wordCarrier_comp D.parent E.parent D.parent_mem E.parent_mem hn hm).symm
  have d := decodeNativeWordCell_get A A'' (E.parent ∘ D.parent)
    (fun _ hu => E.parent_mem _ (D.parent_mem _ hu)) hm (p₀.comp q₀) hC k
  change (D.compose E hn hm hD hE).outer zs[k] (List.getElem_mem _) = _ at d
  rw [d]
  have h := linear_readCompositeWordCell F₀ A A' A'' D.parent E.parent
    D.parent_mem E.parent_mem hxs hn hm p (fun j => E.outer zs[j] (List.getElem_mem _)) k r
  dsimp only at h
  unfold F₀ at h
  simp only [rightFactor_sameCollect R _hR] at h
  exact h

end ParentComposite

set_option backward.isDefEq.respectTransparency false in
/-- A family of raw structural comparisons pastes through the literal
outer chart, with empty groups retained. -/
theorem flat_foreach_cells {X I : Type u} (A : X → C) (B : I → C)
    (P Q : I → GridExpr X) (is : List I)
    (c : ∀ i, GridCircuit X (P i) (Q i))
    (p : ∀ i, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i) ⟶ B i)
    (q : ∀ i, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (Q i) ⟶ B i)
    (_h : ∀ i, GridCircuit.eval (symmetricCross (C:=C)) A (c i) ≫ q i = p i) :
    AddressOrder.mapSum additiveStructure A (gridOrder (GridCircuit.foreach P Q c is)) ≫
      compressGrid A (GridExpr.over Q is) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A Q is) ≫
      act 𝒮 Zₐ q is =
    compressGrid A (GridExpr.over P is) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P is) ≫
      act 𝒮 Zₐ p is := by
  let C₀ := symmetricCross (C:=C)
  let Cc := GridCircuit.foreach P Q c is
  let ex := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A P is
  let ey := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A Q is
  let j := fun i => GridCircuit.eval C₀ A (c i)
  have h := heq_paste ex ey (GridCircuit.foreach_eval C₀ A P Q c is)
  have k := compressGrid_order A Cc
  have t : act 𝒮 Zₐ j is ≫ act 𝒮 Zₐ q is = act 𝒮 Zₐ p is :=
    (act_seq (S:=𝒮) (Z:=Zₐ) j q is).trans (congrArg (fun z => act 𝒮 Zₐ z is) (funext _h))
  change AddressOrder.mapSum additiveStructure A (gridOrder Cc) ≫ compressGrid A (GridExpr.over Q is) ≫
      eqToHom ey ≫ act 𝒮 Zₐ q is = _
  change GridCircuit.eval C₀ A Cc ≫ eqToHom ey = eqToHom ex ≫ act 𝒮 Zₐ j is at h
  rw [reassoc_of% k, reassoc_of% h, t]


section RaggedGroups
variable {T : Bi (coeff (C:=C))} {Q I : Type u}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (A : Q → C) (is : List I) (X Y : I → Type u)
variable (xs : ∀ i, List (X i)) (ys : ∀ i, List (Y i))
variable (P : ∀ i, X i → Y i → GridExpr Q)
variable (V : ∀ i, X i → C) (W : ∀ i, Y i → C) (V' : I → C)
variable (α : ∀ i, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (V i) (xs i) ⟶ V' i)
variable {a b : C}
variable (β : ∀ i, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (W i) (ys i) ⟶ b)
variable (γ : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V' is ⟶ a)

def childMajorGroupTree (i : I) :=
  GridExpr.over (fun y => GridExpr.over (fun x => P i x y) (xs i)) (ys i)

def parentMajorGroupTree (i : I) :=
  GridExpr.over (fun x => GridExpr.over (P i x) (ys i)) (xs i)

def groupExchangeCircuit (i : I) :
    GridCircuit Q (parentMajorGroupTree X Y xs ys P i) (childMajorGroupTree X Y xs ys P i) :=
  GridCircuit.transpose (P i) (ys i) (xs i)

set_option backward.isDefEq.respectTransparency false in
include N NL NR in
/-- The complete fixed-final-fibre non-disjoint exchange in raw flat
charts. The groups and both ragged local axes are independent and may
be empty. The two schedules are defined separately from their cells. -/
theorem flat_grouped_dependent_exchange
    (p : ∀ i x y, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i x y) ⟶ T.obj (V i x) (W i y)) :
    let R₀ := parentMajorGroupTree X Y xs ys P
    let C₀ := childMajorGroupTree X Y xs ys P
    let r := GridCircuit.foreach R₀ C₀ (groupExchangeCircuit X Y xs ys P) is
    let sourceCell := fun i => eqToHom (colMatrix_pin A (P i) (xs i) (ys i)) ≫
      childMajorParentGather R L (V i) (W i)
        (fun x y => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i x y)) (xs i) (ys i) (p i) (α i) ≫
        T.map (𝟙 (V' i)) (β i)
    let row := fun i x =>
      act 𝒮 Zₐ (p i x) (ys i) ≫ (Lin.left L (V i x)).collect (W i) (ys i) ≫ T.map (𝟙 _) (β i)
    let targetCell := fun i => eqToHom (rowMatrix_pin A (P i) (xs i) (ys i)) ≫
      act 𝒮 Zₐ (row i) (xs i) ≫ DependentFibre.gather R (V i) b (xs i)
    AddressOrder.mapSum additiveStructure A (gridOrder r) ≫
      compressGrid A (GridExpr.over C₀ is) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A C₀ is) ≫
      act 𝒮 Zₐ sourceCell is ≫ DependentFibre.gather R V' b is ≫ T.map γ (𝟙 b) =
    compressGrid A (GridExpr.over R₀ is) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) A R₀ is) ≫
      act 𝒮 Zₐ targetCell is ≫ DependentFibre.gather R (fun i => fold 𝒮 Zₐ (V i) (xs i)) b is ≫
      T.map (act 𝒮 Zₐ α is ≫ γ) (𝟙 b) := by
  intro R₀ C₀ r sourceCell row targetCell
  let E := fun i => T.obj (V' i) b
  let q := fun i => targetCell i ≫ T.map (α i) (𝟙 b)
  have h (i : I) : GridCircuit.eval (symmetricCross (C:=C)) A (groupExchangeCircuit X Y xs ys P i) ≫
      sourceCell i = q i := by
    let a := rowMatrix_pin A (P i) (xs i) (ys i)
    let b := colMatrix_pin A (P i) (xs i) (ys i)
    let F := fun x y => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i x y)
    let c := transposeBlock (symmetricCross (C:=C)) F (ys i) (xs i)
    have e := heq_paste a b (GridCircuit.transpose_eval (symmetricCross (C:=C)) A (P i) (ys i) (xs i))
    have k := childMajor_then_continuation (symmetricCross (C:=C)) R L N NL (V i) (W i) F
      (xs i) (ys i) (p i) (α i) (β i)
    change GridCircuit.eval (symmetricCross (C:=C)) A (groupExchangeCircuit X Y xs ys P i) ≫ eqToHom b =
      eqToHom a ≫ c at e
    change _ ≫ eqToHom b ≫ _ = _
    rw [reassoc_of% e]
    have kk := congrArg (fun u => eqToHom a ≫ u) k
    dsimp only [q, targetCell, row, continuationBeforeFirstParent] at *
    simp only [Category.assoc] at kk ⊢
    exact kk
  have H := flat_foreach_cells A E R₀ C₀ is (groupExchangeCircuit X Y xs ys P) q sourceCell h
  rw [reassoc_of% H]
  let v := fun i => T.map (α i) (𝟙 b)
  have k : act 𝒮 Zₐ targetCell is ≫ act 𝒮 Zₐ v is = act 𝒮 Zₐ q is :=
    act_seq (S:=𝒮) (Z:=Zₐ) targetCell v is
  have z := gather_outer NR α b is
  change act 𝒮 Zₐ v is ≫ DependentFibre.gather R V' b is =
    DependentFibre.gather R (fun i => fold 𝒮 Zₐ (V i) (xs i)) b is ≫
      T.map (act 𝒮 Zₐ α is) (𝟙 b) at z
  rw [← k, Category.assoc, reassoc_of% z, bi_map_comp, Category.id_comp]

end RaggedGroups

section GroupData
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')

abbrev IntermediateChild (y : Y) := {v : V // v ∈ vs y}

def intermediateChildRow (t : Z × W) (y : E.Slice t.1) : List (IntermediateChild (vs:=vs) y.val) :=
  (E.terms t.1 t.2 y).pmap Subtype.mk (fun _ hv => (List.mem_filter.mp hv).1)

omit [DecidableEq Y] [DecidableEq V] in
theorem intermediateChildRow_values (t : Z × W) (y : E.Slice t.1) :
    (intermediateChildRow E t y).map Subtype.val = E.terms t.1 t.2 y := by
  unfold intermediateChildRow
  rw [List.map_pmap, List.pmap_eq_map]
  exact List.map_id _

omit [DecidableEq Y] [DecidableEq V] in
theorem intermediateChild_member (t : Z × W) (y : E.Slice t.1) (v : IntermediateChild (vs:=vs) y.val) :
    (y.val,v.val) ∈ dependentWord ys vs :=
  (dependentWord_mem ys vs (y.val,v.val)).mpr ⟨y.property.1,v.property⟩

noncomputable def intermediateChild_index (h : (dependentWord ys vs).Nodup) (t : Z × W)
    (y : E.Slice t.1) (v : IntermediateChild (vs:=vs) y.val) : Fin (dependentWord ys vs).length :=
  (wordPositions (dependentWord ys vs) h).symm ⟨(y.val,v.val),intermediateChild_member E t y v⟩

omit [DecidableEq Y] [DecidableEq V] in
theorem intermediateChild_index_read (h : (dependentWord ys vs).Nodup) (t : Z × W)
    (y : E.Slice t.1) (v : IntermediateChild (vs:=vs) y.val) :
    (dependentWord ys vs)[intermediateChild_index E h t y v] = (y.val,v.val) :=
  congrArg Subtype.val ((wordPositions (dependentWord ys vs) h).apply_symm_apply
    ⟨(y.val,v.val),intermediateChild_member E t y v⟩)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] [DecidableEq V] in
theorem intermediateChildRow_index (h : (dependentWord ys vs).Nodup) (t : Z × W) (y : E.Slice t.1) :
    (intermediateChildRow E t y).map (intermediateChild_index E h t y) = secondChildFinRow E h t y := by
  unfold intermediateChildRow secondChildFinRow
  rw [List.map_pmap]
  exact List.pmap_congr_left _ (fun _ _ _ _ => rfl)

def firstChildGrid (y : Y) (x : D.Slice y) (v : IntermediateChild (vs:=vs) y) : GridExpr (X × U) :=
  GridExpr.over (fun u => .leaf (x.val,u)) (D.terms y v.val x)

set_option backward.isDefEq.respectTransparency false in
theorem firstChildGrid_fibre (y : Y) (v : IntermediateChild (vs:=vs) y) :
    dependentFibreRawTree D (y,v.val) =
      GridExpr.over (fun x => firstChildGrid D y x v) (D.slice y) := by
  unfold dependentFibreRawTree dependentFibreLocalTree dependentExpr firstChildGrid
  simp only [retagGrid_over, retagGrid]
  rfl

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

theorem firstChildGrid_eval (y : Y) (x : D.Slice y) (v : IntermediateChild (vs:=vs) y) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) A B) (firstChildGrid D y x v) =
      rowSource (S:=𝒮) (T:=T) (Z:=Zₐ) (D.parentVal y) (indexInput (D.childVal y) (D.terms y v.val)) x :=
  (GridExpr.eval_over _ _ _).trans (std_fold_map (T.obj (A x.val)) (B x.val) (D.terms y v.val x)).symm

def firstChildGrid_cell (y : Y) (x : D.Slice y) (v : IntermediateChild (vs:=vs) y) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) A B) (firstChildGrid D y x v) ⟶
      T.obj (D.parentVal y x) (B' y v.val) :=
  eqToHom (firstChildGrid_eval (T:=T) D y x v) ≫
    row (D.parentVal y) (indexInput (D.childVal y) (D.terms y v.val)) L (D.locInner y v.val v.property) x


set_option backward.isDefEq.respectTransparency false in
theorem firstCell_grouped
    (y : Y) (hy : y ∈ ys) (v : IntermediateChild (vs:=vs) y) :
    let G := dependentLabels (T:=T) A B
    let P := fun x => firstChildGrid D y x v
    let e := (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) G) (firstChildGrid_fibre D y v)).trans
      (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P (D.slice y))
    dependentFibreRawCell D R L (y,v.val) ((dependentWord_mem ys vs _).mpr ⟨hy,v.property⟩) =
      eqToHom e ≫ act 𝒮 Zₐ (fun x => firstChildGrid_cell D L y x v) (D.slice y) ≫
      DependentFibre.gather R (D.parentVal y) (B' y v.val) (D.slice y) ≫ T.map (D.locOuter y hy) (𝟙 _) := by
  intro G P e
  let F := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (P x)
  let code := indexInput (D.childVal y) (D.terms y v.val)
  let q := fun x => row (D.parentVal y) code L (D.locInner y v.val v.property) x
  let p := fun x => eqToHom (firstChildGrid_eval (T:=T) D y x v)
  let d := congrArg (fun H => fold 𝒮 Zₐ H (D.slice y)) (funext (firstChildGrid_eval (T:=T) D y · v))
  unfold dependentFibreRawCell dep
  change eqToHom _ ≫ eqToHom _ ≫ act 𝒮 Zₐ q (D.slice y) ≫
      DependentFibre.gather R (D.parentVal y) (B' y v.val) (D.slice y) ≫ T.map (D.locOuter y hy) (𝟙 _) =
    eqToHom e ≫ act 𝒮 Zₐ (fun x => p x ≫ q x) (D.slice y) ≫
      DependentFibre.gather R (D.parentVal y) (B' y v.val) (D.slice y) ≫ T.map (D.locOuter y hy) (𝟙 _)
  have j : act 𝒮 Zₐ p (D.slice y) ≫ act 𝒮 Zₐ q (D.slice y) =
      act 𝒮 Zₐ (fun x => p x ≫ q x) (D.slice y) := act_seq (S:=𝒮) (Z:=Zₐ) p q _
  rw [← reassoc_of% j]
  have hd : act 𝒮 Zₐ p (D.slice y) = eqToHom d :=
    std_act_eqToHom (fun x => firstChildGrid_eval (T:=T) D y x v) (D.slice y)
  rw [hd]
  simp only [eqToHom_trans_assoc]


theorem gatherLeft_eq_collect (a : C) (l : List C) :
    gatherLeft L a l = (Lin.left L a).collect id l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    change (coeff (C:=C)).seq ((𝒮).map (𝟙 (T.obj a b)) (gatherLeft L a l)) (L.cons _ _ _) =
      (coeff (C:=C)).seq ((𝒮).map (𝟙 (T.obj a b)) ((Lin.left L a).collect id l)) (L.cons _ _ _)
    rw [ih]

omit [DecidableEq Y] [DecidableEq V] in
theorem secondChild_values (t : Z × W) (y : E.Slice t.1) :
    (intermediateChildRow E t y).map (fun v => B' y.val v.val) =
      ((E.terms t.1 t.2 y).map (B' y.val)) := by
  exact (List.map_map (f:=Subtype.val) (g:=B' y.val) (l:=intermediateChildRow E t y)).symm.trans
    (congrArg (List.map (B' y.val)) (intermediateChildRow_values E t y))

omit [DecidableEq Y] [DecidableEq V] in
theorem secondChildFold_pin (t : Z × W) (y : E.Slice t.1) :
    fold 𝒮 Zₐ (fun v => B' y.val v.val) (intermediateChildRow E t y) =
      inner (S:=𝒮) (Z:=Zₐ) (indexInput (E.childVal t.1) (E.terms t.1 t.2)) y :=
  (std_fold_map id (fun (v : IntermediateChild (vs:=vs) y.val) => B' y.val v.val) (intermediateChildRow E t y)).symm.trans
    (congrArg (fold 𝒮 Zₐ id) (secondChild_values E t y))

def secondChildCell (t : Z × W) (ht : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    fold 𝒮 Zₐ (fun v => B' y.val v.val) (intermediateChildRow E t y) ⟶ B'' t.1 t.2 :=
  eqToHom (secondChildFold_pin E t y) ≫ E.locInner t.1 t.2 ht y

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] [DecidableEq V] in
theorem secondChildAttached_cell (t : Z × W) (ht : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    HEq ((Lin.left L (A' y.val)).collect (fun v => B' y.val v.val) (intermediateChildRow E t y) ≫
      T.map (𝟙 (A' y.val)) (secondChildCell E t ht y))
      (row (E.parentVal t.1) (indexInput (E.childVal t.1) (E.terms t.1 t.2)) L (E.locInner t.1 t.2 ht) y) := by
  let F := Lin.left L (A' y.val)
  let x := A' y.val
  let l := intermediateChildRow E t y
  let b := fun (v : IntermediateChild (vs:=vs) y.val) => B' y.val v.val
  let z := B'' t.1 t.2
  let s := (E.terms t.1 t.2 y).map (B' y.val)
  let β := E.locInner t.1 t.2 ht y
  let k := secondChildFold_pin E t y
  have e := (std_fold_map (T.obj x) b l).symm.trans
    (congrArg (fold 𝒮 Zₐ (T.obj x)) (secondChild_values E t y))
  have p : HEq (F.collect b l) (gatherLeft L x s) := by
    rw [gatherLeft_eq_collect]
    have z {q₀ q₁ : List C} (e : q₀ = q₁) : HEq (F.collect id q₀) (F.collect id q₁) := by cases e; rfl
    exact (linCollect_map_heq F id b l).trans (z (secondChild_values E t y))
  have q : HEq (T.map (𝟙 x) (secondChildCell E t ht y)) (T.map (𝟙 x) β) :=
    biMap_heq (T:=T) rfl rfl k rfl HEq.rfl (hom_source_pin_heq k β)
  exact structural_seq_heq (K:=coeff (C:=C)) e (congrArg (T.obj x) k) rfl p q


set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] [DecidableEq V] in
theorem secondCell_grouped_heq (h : (dependentWord ys vs).Nodup) (t : Z × W)
    (ht : t ∈ dependentWord zs ws) :
    let k := (dependentWord_mem zs ws t).mp ht
    let is := E.slice t.1
    let V₀ := E.parentVal t.1
    let b := B'' t.1 t.2
    let q := fun y : E.Slice t.1 =>
      (Lin.left L (V₀ y)).collect (fun v => B' y.val v.val) (intermediateChildRow E t y) ≫
        T.map (𝟙 (V₀ y)) (secondChildCell E t k.2 y)
    HEq (dependentFibreIndexCell E R L h t ht)
      (act 𝒮 Zₐ q is ≫ DependentFibre.gather R V₀ b is ≫ T.map (E.locOuter t.1 k.1) (𝟙 b)) := by
  intro k is V₀ b q
  let J := indexInput (E.childVal t.1) (E.terms t.1 t.2)
  let U := fun y => rowSource (S:=𝒮) (T:=T) (Z:=Zₐ) V₀ J y
  let F := fun y : E.Slice t.1 =>
    fold 𝒮 Zₐ (fun v => T.obj (V₀ y) (B' y.val v.val)) (intermediateChildRow E t y)
  let r := row V₀ J L (E.locInner t.1 t.2 k.2)
  have e (y : E.Slice t.1) : F y = U y :=
    (std_fold_map (T.obj (V₀ y)) (fun v => B' y.val v.val) (intermediateChildRow E t y)).symm.trans
      (congrArg (fold 𝒮 Zₐ (T.obj (V₀ y))) (secondChild_values E t y))
  have c : HEq (act 𝒮 Zₐ q is) (act 𝒮 Zₐ r is) :=
    actFamily_heq (funext e) rfl (secondChildAttached_cell E L t k.2) is
  let τ := DependentFibre.gather R V₀ b is ≫ T.map (E.locOuter t.1 k.1) (𝟙 b)
  have d := structural_seq_heq (K:=coeff (C:=C)) (congrArg (fun K => fold 𝒮 Zₐ K is) (funext e)) rfl rfl c
    (show HEq τ τ from HEq.rfl)
  have q₀ : HEq (dependentFibreIndexCell E R L h t ht) (act 𝒮 Zₐ r is ≫ τ) := by
    unfold dependentFibreIndexCell dependentFibreRawCell
    exact (hom_source_pin_heq _ _).trans ((hom_source_pin_heq _ _).trans (hom_source_pin_heq _ _))
  exact q₀.trans d.symm


set_option backward.isDefEq.respectTransparency false in
theorem actE_over_decode_any {I : Type w} {X : Type z} {A B : I → C} (p : ∀ t, A t ⟶ B t)
    (G : X → GridExpr I) {P Q : X → C}
    (ea : ∀ x, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (G x) = P x)
    (eb : ∀ x, GridExpr.eval (S:=𝒮) (Z:=Zₐ) B (G x) = Q x)
    (q : ∀ x, P x ⟶ Q x) (_h : ∀ x, HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p (G x)) (q x)) (l : List X) :
    HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p (GridExpr.over G l)) (act 𝒮 Zₐ q l) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [GridExpr.over, GridExpr.actE, act]
    exact structural_map_heq (S:=𝒮) (ea a) (eb a)
      ((GridExpr.eval_over A G as).trans (congrArg (fun F => fold 𝒮 Zₐ F as) (funext ea)))
      ((GridExpr.eval_over B G as).trans (congrArg (fun F => fold 𝒮 Zₐ F as) (funext eb)))
      (_h a) ih

set_option backward.isDefEq.respectTransparency false in
theorem actE_leafOver_heq {I : Type w} {A B : I → C} (p : ∀ t, A t ⟶ B t) (xs : List I) :
    HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p (GridExpr.over GridExpr.leaf xs)) (act 𝒮 Zₐ p xs) :=
  actE_over_decode_any p GridExpr.leaf (fun _ => rfl) (fun _ => rfl) p (fun _ => HEq.rfl) xs

def firstChildColumn (y : Y) (hy : y ∈ ys) (v : IntermediateChild (vs:=vs) y) :
    fold 𝒮 Zₐ (fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) A B)
      (firstChildGrid D y x v)) (D.slice y) ⟶ T.obj (A' y) (B' y v.val) :=
  act 𝒮 Zₐ (fun x => firstChildGrid_cell D L y x v) (D.slice y) ≫
    DependentFibre.gather R (D.parentVal y) (B' y v.val) (D.slice y) ≫ T.map (D.locOuter y hy) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
theorem firstCell_grouped_heq (y : Y) (hy : y ∈ ys) (v : IntermediateChild (vs:=vs) y) :
    HEq (dependentFibreRawCell D R L (y,v.val) ((dependentWord_mem ys vs _).mpr ⟨hy,v.property⟩))
      (firstChildColumn D R L y hy v) := by
  have h := firstCell_grouped D R L y hy v
  dsimp only at h
  exact (heq_of_eq h).trans (hom_source_pin_heq _ _)

set_option backward.isDefEq.respectTransparency false in
theorem firstCells_grouped_heq (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    let e := dependentFibreIndexTree E h t
    let p := fun j : Fin (dependentWord ys vs).length =>
      dependentFibreRawCell D R L (dependentWord ys vs)[j] (List.getElem_mem _)
    HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e)
      (act 𝒮 Zₐ (fun y : E.Slice t.1 =>
        act 𝒮 Zₐ (firstChildColumn D R L y.val y.property.1) (intermediateChildRow E t y)) (E.slice t.1)) := by
  intro e p
  let G := dependentLabels (T:=T) A B
  let yw := dependentWord ys vs
  let I := E.Slice t.1
  let A₀ := fun j : Fin yw.length => GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (dependentFibreRawTree D yw[j])
  let B₀ := fun j : Fin yw.length => dependentLabels (T:=T) A' B' yw[j]
  let xa := fun y : I => D.slice y.val
  let ya := fun y : I => intermediateChildRow E t y
  let idx := fun y : I => intermediateChild_index E h t y
  let g := fun y : I => GridExpr.over GridExpr.leaf (secondChildFinRow E h t y)
  let U := fun y : I => fun v : IntermediateChild (vs:=vs) y.val =>
    fold 𝒮 Zₐ (fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (firstChildGrid D y.val x v)) (xa y)
  let V₀ := fun y : I => fun v : IntermediateChild (vs:=vs) y.val => T.obj (A' y.val) (B' y.val v.val)
  let q := fun y : I => firstChildColumn D R L y.val y.property.1
  have ea (y : I) (v : IntermediateChild (vs:=vs) y.val) : A₀ (idx y v) = U y v := by
    have e := (congrArg (dependentFibreRawTree D) (intermediateChild_index_read E h t y v)).trans
      (firstChildGrid_fibre D y.val v)
    exact (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) G) e).trans
      (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G (fun x => firstChildGrid D y.val x v) (xa y))
  have eb (y : I) (v : IntermediateChild (vs:=vs) y.val) : B₀ (idx y v) = V₀ y v :=
    congrArg (dependentLabels (T:=T) A' B') (intermediateChild_index_read E h t y v)
  have mp (y : I) (v : IntermediateChild (vs:=vs) y.val) : HEq (p (idx y v)) (q y v) := by
    have k {x x' : Y × V} (e : x = x') (hx : x ∈ yw) (hx' : x' ∈ yw) :
        HEq (dependentFibreRawCell D R L x hx) (dependentFibreRawCell D R L x' hx') := by cases e; rfl
    exact (k (intermediateChild_index_read E h t y v) (List.getElem_mem _)
      (intermediateChild_member E t y v)).trans (firstCell_grouped_heq D R L y.val y.property.1 v)
  have obj (K : Fin yw.length → C)
      (H : ∀ y : I, IntermediateChild (vs:=vs) y.val → C)
      (j : ∀ y v, K (idx y v) = H y v) (y : I) :
      GridExpr.eval (S:=𝒮) (Z:=Zₐ) K (g y) = fold 𝒮 Zₐ (H y) (ya y) := by
    let w := intermediateChildRow_index E h t y
    have e₁ := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) K GridExpr.leaf (secondChildFinRow E h t y)
    have e₂ := (congrArg (fold 𝒮 Zₐ K) w).symm
    have e₃ := std_fold_map K (idx y) (ya y)
    have e₄ := congrArg (fun F => fold 𝒮 Zₐ F (ya y)) (funext (j y))
    exact e₁.trans (e₂.trans (e₃.trans e₄))
  change HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p (dependentFibreIndexTree E h t)) _
  rw [dependentFibreIndexTree_over]
  apply actE_over_decode_any p g (obj A₀ U ea) (obj B₀ V₀ eb)
  intro y
  refine (actE_leafOver_heq p (secondChildFinRow E h t y)).trans ?_
  have m := (actRetag_heq (idx y) p (ya y)).symm
  rw [intermediateChildRow_index E h t y] at m
  exact m.trans (actFamily_heq (funext (ea y)) (funext (eb y)) (mp y) (ya y))


abbrev groupsP (t : Z × W) := fun y : E.Slice t.1 => D.Slice y.val
abbrev groupsQ (t : Z × W) := fun y : E.Slice t.1 => IntermediateChild (vs:=vs) y.val

def dependentChildMajorTree (t : Z × W) : GridExpr (X × U) :=
  GridExpr.over (childMajorGroupTree (groupsP D E t) (groupsQ E t)
    (fun y => D.slice y.val) (intermediateChildRow E t)
    (fun y => firstChildGrid D y.val)) (E.slice t.1)

def dependentParentMajorTree (t : Z × W) : GridExpr (X × U) :=
  GridExpr.over (parentMajorGroupTree (groupsP D E t) (groupsQ E t)
    (fun y => D.slice y.val) (intermediateChildRow E t)
    (fun y => firstChildGrid D y.val)) (E.slice t.1)

set_option backward.isDefEq.respectTransparency false in
theorem sequentialDependentFibreTree_group (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    sequentialDependentFibreTree D E h t = dependentChildMajorTree D E t := by
  rw [sequentialDependentFibreTree_shape]
  unfold dependentChildMajorTree childMajorGroupTree
  congr 1
  funext y
  rw [← intermediateChildRow_values E t y, gridOver_map]
  exact congrArg (fun f => GridExpr.over f (intermediateChildRow E t y))
    (funext (fun v => firstChildGrid_fibre D y.val v))

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] [DecidableEq V] in
theorem secondIndexTree_groupEval (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    let yw := dependentWord ys vs
    let G := fun i : Fin yw.length => dependentLabels (T:=T) A' B' yw[i]
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (dependentFibreIndexTree E h t) =
      fold 𝒮 Zₐ (fun y : E.Slice t.1 =>
        fold 𝒮 Zₐ (fun v => T.obj (A' y.val) (B' y.val v.val)) (intermediateChildRow E t y))
        (E.slice t.1) := by
  intro yw G
  rw [dependentFibreIndexTree_over, GridExpr.eval_over]
  apply congrArg (fun F => fold 𝒮 Zₐ F (E.slice t.1))
  funext y
  rw [GridExpr.eval_over, ← intermediateChildRow_index E h t y]
  let r := intermediateChildRow E t y
  let i := intermediateChild_index E h t y
  refine (std_fold_map G i r).trans ?_
  apply congrArg (fun F => fold 𝒮 Zₐ F r)
  funext v
  exact congrArg (dependentLabels (T:=T) A' B') (intermediateChild_index_read E h t y v)


def groupedSecondSourceCell (t : Z × W) (ht : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) A B)
        (childMajorGroupTree (groupsP D E t) (groupsQ E t)
          (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val) y) ⟶
      T.obj (A' y.val) (B'' t.1 t.2) :=
  let a := dependentLabels (T:=T) A B
  let P := firstChildGrid D y.val
  let xs := D.slice y.val
  let ys := intermediateChildRow E t y
  eqToHom (colMatrix_pin a P xs ys) ≫
    childMajorParentGather R L (D.parentVal y.val) (fun v => B' y.val v.val)
      (fun x v => GridExpr.eval (S:=𝒮) (Z:=Zₐ) a (P x v)) xs ys (firstChildGrid_cell D L y.val)
      (D.locOuter y.val y.property.1) ≫ T.map (𝟙 (A' y.val)) (secondChildCell E t ht y)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
theorem sequentialDependent_grouped_tail
    (h : (dependentWord ys vs).Nodup) (t : Z × W) (ht : t ∈ dependentWord zs ws) :
    let k := (dependentWord_mem zs ws t).mp ht
    let a := dependentLabels (T:=T) A B
    let yword := dependentWord ys vs
    let P := fun j : Fin yword.length => dependentFibreRawTree D yword[j]
    let e := dependentFibreIndexTree E h t
    let p := fun j : Fin yword.length => dependentFibreRawCell D R L yword[j] (List.getElem_mem _)
    let q := dependentFibreIndexCell E R L h t ht
    let G := childMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    let d := (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) a) (sequentialDependentFibreTree_group D E h t)).trans
      (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) a G (E.slice t.1))
    eqToHom (graftGrid_eval a P e) ≫ GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e ≫ q =
      eqToHom d ≫ act 𝒮 Zₐ (groupedSecondSourceCell D E R L t k.2) (E.slice t.1) ≫
        DependentFibre.gather R (E.parentVal t.1) (B'' t.1 t.2) (E.slice t.1) ≫
        T.map (E.locOuter t.1 k.1) (𝟙 _) := by
  intro k a yword P e p q G d
  let I := E.Slice t.1
  let is := E.slice t.1
  let z := B'' t.1 t.2
  let S := dependentChildMajorTree D E t
  let ξ := fun y : I => colMatrix_pin a (firstChildGrid D y.val) (D.slice y.val) (intermediateChildRow E t y)
  let acts := fun y : I => act 𝒮 Zₐ (firstChildColumn D R L y.val y.property.1) (intermediateChildRow E t y)
  let post := fun y : I =>
    (Lin.left L (A' y.val)).collect (fun v => B' y.val v.val) (intermediateChildRow E t y) ≫
      T.map (𝟙 (A' y.val)) (secondChildCell E t k.2 y)
  let rest := DependentFibre.gather R (E.parentVal t.1) z is ≫ T.map (E.locOuter t.1 k.1) (𝟙 z)
  let U := fun y : I => GridExpr.eval (S:=𝒮) (Z:=Zₐ) a (G y)
  let ξ₀ := congrArg (fun J => fold 𝒮 Zₐ J is) (funext ξ)
  let step := fun y : I => acts y ≫ post y
  let la := (graftGrid_eval a P e).symm.trans (d.trans ξ₀)
  let lb := secondIndexTree_groupEval (T:=T) E h t
  have H := structural_seq_heq (K:=coeff (C:=C)) la lb rfl
    (firstCells_grouped_heq D E R L h t) (secondCell_grouped_heq E R L h t ht)
  have H' : (GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e) ≫ q =
      eqToHom la ≫ (act 𝒮 Zₐ acts is ≫ act 𝒮 Zₐ post is ≫ rest) := by
    have k := heq_paste la rfl H
    change ((GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e) ≫ q) ≫ 𝟙 _ =
        eqToHom la ≫ (act 𝒮 Zₐ acts is ≫ (act 𝒮 Zₐ post is ≫ rest)) at k
    rw [Category.comp_id] at k
    exact k
  rw [H', ← Category.assoc (eqToHom (graftGrid_eval a P e)), eqToHom_trans]
  have ePin : (graftGrid_eval a P e).trans la = d.trans ξ₀ := Subsingleton.elim _ _
  rw [ePin, ← eqToHom_trans d ξ₀]
  have c : act 𝒮 Zₐ acts is ≫ act 𝒮 Zₐ post is = act 𝒮 Zₐ step is :=
    act_seq (S:=𝒮) (Z:=Zₐ) acts post is
  have j : act 𝒮 Zₐ (fun y => eqToHom (ξ y)) is = eqToHom ξ₀ := std_act_eqToHom ξ is
  have l : act 𝒮 Zₐ (fun y => eqToHom (ξ y)) is ≫ act 𝒮 Zₐ step is =
      act 𝒮 Zₐ (fun y => eqToHom (ξ y) ≫ step y) is :=
    act_seq (S:=𝒮) (Z:=Zₐ) (fun y => eqToHom (ξ y)) step is
  simp only [Category.assoc]
  rw [reassoc_of% c, ← j, reassoc_of% l]
  have M (y : I) : eqToHom (ξ y) ≫ step y = groupedSecondSourceCell D E R L t k.2 y := by
    unfold step acts post groupedSecondSourceCell childMajorParentGather firstChildColumn
    simp only [Category.assoc]
  rw [show (fun y => eqToHom (ξ y) ≫ step y) = groupedSecondSourceCell D E R L t k.2 from funext M]


noncomputable def sequential_group_order (h : (dependentWord ys vs).Nodup)
    (h' : (dependentWord zs ws).Nodup) (k : Fin (dependentWord zs ws).length) :
    AddressOrder (X × U)
      (wordFibre (dependentWord xs us) (origDepCarrier E ∘ origDepCarrier D) (dependentWord zs ws)[k])
      (dependentParentMajorTree D E (dependentWord zs ws)[k]).leaves := by
  let t := (dependentWord zs ws)[k]
  let ra := sequentialDependentFibreOrder D E h h' k
  let d := sequentialDependentFibreTree_group D E h t
  let F := groupExchangeCircuit (groupsP D E t) (groupsQ E t) (fun y => D.slice y.val)
    (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
  let e := GridCircuit.foreach _ _ F (E.slice t.1)
  exact ((ra.seq (castOrder (congrArg GridExpr.leaves d))).seq (Classical.choice (AddressOrder.ofPerm (gridOrder e).perm.symm)))

def groupedFirstSourceCell (t : Z × W) (ht : t.2 ∈ ws t.1) (y : E.Slice t.1) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) A B)
        (parentMajorGroupTree (groupsP D E t) (groupsQ E t)
          (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val) y) ⟶
      T.obj (fold 𝒮 Zₐ (D.parentVal y.val) (D.slice y.val)) (B'' t.1 t.2) :=
  let a := dependentLabels (T:=T) A B
  let P := firstChildGrid D y.val
  let xs := D.slice y.val
  let ys := intermediateChildRow E t y
  eqToHom (rowMatrix_pin a P xs ys) ≫
    act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (firstChildGrid_cell D L y.val x) ys ≫
      (Lin.left L (D.parentVal y.val x)).collect (fun v => B' y.val v.val) ys ≫
      T.map (𝟙 (D.parentVal y.val x)) (secondChildCell E t ht y)) xs ≫
    DependentFibre.gather R (D.parentVal y.val) (B'' t.1 t.2) xs

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2700000 in
theorem sequentialDependent_normalized_coefficient
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    (h₀ : (dependentWord xs us).Nodup) (h : (dependentWord ys vs).Nodup)
    (h' : (dependentWord zs ws).Nodup) (k : Fin (dependentWord zs ws).length) :
    let zw := dependentWord zs ws
    let t := zw[k]
    let ht := (dependentWord_mem zs ws t).mp (List.getElem_mem _)
    let G₀ := dependentLabels (T:=T) A B
    let G₂ := dependentLabels (T:=T) A'' B''
    let is := E.slice t.1
    let V := fun y : E.Slice t.1 => fold 𝒮 Zₐ (D.parentVal y.val) (D.slice y.val)
    let γ := act 𝒮 Zₐ (fun y : E.Slice t.1 => D.locOuter y.val y.property.1) is ≫ E.locOuter t.1 ht.1
    let F := parentMajorGroupTree (groupsP D E t) (groupsQ E t)
      (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    let supp := fun x hx => origDepCarrier_support E _ (origDepCarrier_support D x hx)
    let eq := (wordCarrier_comp (origDepCarrier D) (origDepCarrier E) (origDepCarrier_support D)
      (origDepCarrier_support E) h h').symm
    readNativeWordCell G₀ G₂ (origDepCarrier E ∘ origDepCarrier D) supp h'
      ((origDependentWordMap D R L h).comp (origDependentWordMap E R L h')) eq k =
    AddressOrder.mapSum additiveStructure G₀ (sequential_group_order D E h h' k) ≫
      compressGrid G₀ (dependentParentMajorTree D E t) ≫ eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G₀ F is) ≫
      act 𝒮 Zₐ (groupedFirstSourceCell D E R L t ht.2) is ≫ DependentFibre.gather R V (B'' t.1 t.2) is ≫
        T.map γ (𝟙 _) := by
  intro zw t ht G₀ G₂ is V γ F supp eq
  let q := sequentialDependentFibreOrder D E h h' k
  let u := sequential_group_order D E h h' k
  let P' := childMajorGroupTree (groupsP D E t) (groupsQ E t)
    (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
  let c := GridCircuit.foreach F P' (groupExchangeCircuit (groupsP D E t) (groupsQ E t)
    (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)) is
  let z := sequentialDependentFibreTree_group D E h t
  let src := sequentialDependentFibreTree D E h t
  let mid := dependentChildMajorTree D E t
  let β := congrArg GridExpr.leaves z
  let α := congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) G₀) z
  let col := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G₀ P' is
  have h₁ := sequentialDependentFibre_read D E R L h₀ h h' k
  have h₂ := sequentialDependent_grouped_tail D E R L h t (List.getElem_mem _)
  dsimp only at h₁ h₂
  rw [h₁, h₂, ← eqToHom_trans α col]
  have H {a b : GridExpr (X × U)} (z : a = b) :
      compressGrid G₀ a ≫ eqToHom (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) G₀) z) =
        eqToHom (congrArg (fold 𝒮 Zₐ G₀) (congrArg GridExpr.leaves z)) ≫ compressGrid G₀ b := by
    cases z
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have h₃ : compressGrid G₀ src ≫ eqToHom α =
      eqToHom (congrArg (fold 𝒮 Zₐ G₀) β) ≫ compressGrid G₀ mid := H z
  simp only [Category.assoc]
  change AddressOrder.mapSum additiveStructure G₀ q ≫ compressGrid G₀ src ≫ eqToHom α ≫ _ = _
  rw [reassoc_of% h₃]
  have e : AddressOrder.mapSum additiveStructure G₀ q ≫ eqToHom (congrArg (fold 𝒮 Zₐ G₀) β) =
      AddressOrder.mapSum additiveStructure G₀ u ≫ AddressOrder.mapSum additiveStructure G₀ (gridOrder c) := by
    have h := tagged_permutation_coherent G₀ (h₀.filter _) (q.seq (castOrder β)) (u.seq (gridOrder c))
    change AddressOrder.mapSum additiveStructure G₀ q ≫ AddressOrder.mapSum additiveStructure G₀ (castOrder β) =
      AddressOrder.mapSum additiveStructure G₀ u ≫ AddressOrder.mapSum additiveStructure G₀ (gridOrder c) at h
    rw [castOrder_map] at h
    exact h
  rw [reassoc_of% e]
  have y := flat_grouped_dependent_exchange R L N NR NL G₀ is (groupsP D E t) (groupsQ E t)
    (fun y => D.slice y.val) (intermediateChildRow E t) (fun y => firstChildGrid D y.val)
    (fun y => D.parentVal y.val) (fun y v => B' y.val v.val) (E.parentVal t.1)
    (fun y => D.locOuter y.val y.property.1) (secondChildCell E t ht.2) (E.locOuter t.1 ht.1)
    (fun y => firstChildGrid_cell D L y.val)
  dsimp only at y
  exact congrArg (fun f => AddressOrder.mapSum additiveStructure G₀ u ≫ f) y

end GroupData

set_option backward.isDefEq.respectTransparency false in
theorem foldCollect_read {X : Type w} {Y : Type z} (F : Lin 𝒮 Zₐ)
    (B : Y → C) (f : X → Y) (xs : List X) {ys : List Y} (e : xs.map f = ys) :
    let b := (std_fold_map B f xs).symm.trans (congrArg (fold 𝒮 Zₐ B) e)
    let G := fun y => F.obj (B y)
    let a := (std_fold_map G f xs).symm.trans (congrArg (fold 𝒮 Zₐ G) e)
    Lin.collect F (B ∘ f) xs ≫ eqToHom (congrArg F.obj b) = eqToHom a ≫ Lin.collect F B ys := by
  subst ys
  exact heq_paste _ _ (linCollect_map_heq F B f xs)

set_option backward.isDefEq.respectTransparency false in
theorem linear_partition_read_indices {X : Type u} {J : Type w} {K : Type z}
    (F : C ⥤ C) [F.LaxMonoidal]
    (A : X → C) (B : K → C) (L : K → List X) (f : J → K)
    (is : List J) {js : List K} (h : is.map f = js)
    (p : ∀ j, fold 𝒮 Zₐ A (L j) ⟶ B j)
    {a : C} (q : fold 𝒮 Zₐ B js ⟶ a) :
    let G := fun x => F.obj (A x)
    let e := (List.flatMap_map f L is).symm.trans (congrArg (fun l => l.flatMap L) h)
    let b := (std_fold_map B f is).symm.trans (congrArg (fold 𝒮 Zₐ B) h)
    let p₀ := fun j => Lin.collect (linearFunctor F) A (L j) ≫ F.map (p j)
    eqToHom (congrArg (fold 𝒮 Zₐ G) e) ≫ rowsChart G L js ≫ act 𝒮 Zₐ p₀ js ≫
      Lin.collect (linearFunctor F) B js ≫ F.map q =
    rowsChart G (L ∘ f) is ≫ act 𝒮 Zₐ (fun j => p₀ (f j)) is ≫
      Lin.collect (linearFunctor F) (B ∘ f) is ≫ F.map (eqToHom b ≫ q) := by
  intro G e b p₀
  let K := linearFunctor F
  let B₀ := fun j => F.obj (B j)
  let c := (std_fold_map B₀ f is).symm.trans (congrArg (fold 𝒮 Zₐ B₀) h)
  have k := rowsChart_index_apply G L f p₀ is h
  have k' : rowsChart G (L ∘ f) is ≫ act 𝒮 Zₐ (fun j => p₀ (f j)) is ≫ eqToHom c =
      eqToHom (congrArg (fold 𝒮 Zₐ G) e) ≫ rowsChart G L js ≫ act 𝒮 Zₐ p₀ js := k
  rw [← reassoc_of% k']
  have l := foldCollect_read K B f is h
  have l' : Lin.collect K (B ∘ f) is ≫ eqToHom (congrArg F.obj b) =
      eqToHom c ≫ Lin.collect K B js := l
  rw [← reassoc_of% l', F.map_comp]
  have m : eqToHom (congrArg F.obj b) = F.map (eqToHom b) := by
    have H {x y : C} (b : x = y) : eqToHom (congrArg F.obj b) = F.map (eqToHom b) := by
      cases b
      simp only [eqToHom_refl, F.map_id]
    exact H b
  rw [m]


section LocalIndex
variable {Y V Z W : Type u} [DecidableEq Z] [DecidableEq W]
variable {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : Y → C} {B : Y → V → C} {A' : Z → C} {B' : Z → W → C}
variable (E : OrderedDependentMap ys vs zs ws A B A' B')

noncomputable def localContinuationIndex {y : Y} (h : (vs y).Nodup)
    (v : IntermediateChild (vs:=vs) y) : Fin (vs y).length :=
  (wordPositions (vs y) h).symm v

theorem localContinuationIndex_read {y : Y} (h : (vs y).Nodup)
    (v : IntermediateChild (vs:=vs) y) : (vs y)[localContinuationIndex h v] = v.val :=
  congrArg Subtype.val ((wordPositions (vs y) h).apply_symm_apply v)

set_option backward.isDefEq.respectTransparency false in
theorem localIntermediateChildRow_index (y : Y) (h : y ∈ ys)
    (h₀ : (vs y).Nodup) (h₁ : (ws (E.parent y)).Nodup)
    (k : Fin (ws (E.parent y)).length) :
    let t := (E.parent y,(ws (E.parent y))[k])
    let yy : E.Slice (E.parent y) := ⟨y,h,rfl⟩
    (intermediateChildRow E t yy).map (localContinuationIndex h₀) =
      fibreList (wordCarrier (E.child y) (E.child_mem y h) h₁) k := by
  intro t yy
  let g := wordCarrier (E.child y) (E.child_mem y h) h₁
  let f := fun i : Fin (vs y).length => (vs y)[i]
  let l := intermediateChildRow E t yy
  have hf : Function.Injective f := fun i j e => Fin.ext (h₀.getElem_inj.mp e)
  apply (List.map_inj_right (f:=f) (fun _ _ e => hf e)).mp
  rw [List.map_map]
  have hq : f ∘ localContinuationIndex h₀ = (Subtype.val : IntermediateChild (vs:=vs) y → V) :=
    funext (localContinuationIndex_read h₀)
  rw [hq]
  exact (intermediateChildRow_values E t yy).trans ((wordCarrier_fibre (E.child y) (E.child_mem y h) h₁ k).symm)

end LocalIndex

section DirectChildRow
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable {T : Bi (coeff (C:=C))}
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem directChildRow_position
    (hn : ys.Nodup) (hm : zs.Nodup)
    (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
    (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
    (x : X) (hx : x ∈ xs) (hxs : (us x).Nodup)
    [(leftFactor T (A x)).LaxBraided] (_hL : SameLeftGather T (A x) L)
    (k : Fin (ws (E.parent (D.parent x))).length)
    (r : let y := D.parent x
      let t := (E.parent y,(ws (E.parent y))[k])
      let y₀ : E.Slice t.1 := ⟨y,D.parent_mem x hx,rfl⟩
      AddressOrder U
        (childFibreA us (fun x => E.child (D.parent x) ∘ D.child x) t.2 x)
        ((intermediateChildRow E t y₀).flatMap (fun v => childFibreA us D.child v.val x))) :
    let y := D.parent x
    let t := (E.parent y,(ws (E.parent y))[k])
    let y₀ : E.Slice t.1 := ⟨y,D.parent_mem x hx,rfl⟩
    let x₀ : D.Slice y := ⟨x,hx,rfl⟩
    let F := Lin.left L (A x)
    let G := fun u => T.obj (A x) (B x u)
    let Q := fun (v : IntermediateChild (vs:=vs) y) => childFibreA us D.child v.val x
    let s := intermediateChildRow E t y₀
    F.collect (B x) (childFibreA us (fun x => E.child (D.parent x) ∘ D.child x) t.2 x) ≫
      T.map (𝟙 (A x)) ((D.compose E hn hm hD hE).inner x hx t.2 (List.getElem_mem _)) =
    AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q s ≫
      act 𝒮 Zₐ (fun v => attachedSliceChildCell D L x₀ v.val v.property) s ≫
      F.collect (fun v => B' y v.val) s ≫ T.map (𝟙 (A x)) (secondChildCell E t (List.getElem_mem _) y₀) := by
  intro y t y₀ x₀ F G Q s
  let a := A x
  let Lf := leftFactor T a
  let hg := D.parent_mem x hx
  let f := localContinuationIndex (hD x hx)
  let g := wordCarrier (E.child y) (E.child_mem y hg) (hE y hg)
  let v := fibreList g k
  let B₀ := fun j : Fin (vs y).length => B' y (vs y)[j]
  let P₀ := fun j : Fin (vs y).length => childFibreA us D.child (vs y)[j] x
  let p := fun j : Fin (vs y).length => D.inner x hx (vs y)[j] (List.getElem_mem _)
  let q := eqToHom (wordCarrier_fibre_pin (E.child y) (E.child_mem y hg) (hE y hg) (B' y) k) ≫
    E.inner y hg t.2 (List.getElem_mem _)
  have e : s.map f = v := localIntermediateChildRow_index E y hg (hD x hx) (hE y hg) k
  have eqQ (b : IntermediateChild (vs:=vs) y) : Q b = P₀ (f b) :=
    congrArg (fun j => childFibreA us D.child j x) (localContinuationIndex_read (hD x hx) b).symm
  let d₁ : s.flatMap Q = s.flatMap (P₀ ∘ f) := congrArg (fun h => s.flatMap h) (funext eqQ)
  let d₂ : s.flatMap (P₀ ∘ f) = v.flatMap P₀ :=
    (List.flatMap_map f P₀ s).symm.trans (congrArg (fun s => s.flatMap P₀) e)
  let r₀ := r.seq (castOrder (d₁.trans d₂))
  have d := compositeChild_linear_read D E L hn hm hD hE x hx hxs _hL k r₀
  dsimp only at d
  rw [d]
  have rate :
      AddressOrder.mapSum additiveStructure G r₀ =
        AddressOrder.mapSum additiveStructure G r ≫ eqToHom (congrArg (fold 𝒮 Zₐ G) (d₁.trans d₂)) := by
    change AddressOrder.mapSum additiveStructure G r ≫
      AddressOrder.mapSum additiveStructure G (castOrder (d₁.trans d₂)) = _
    rw [castOrder_map]
  rw [rate]
  simp only [Category.assoc]
  have trans := linear_partition_read_indices Lf (B x) B₀ P₀ f s e p q
  dsimp only at trans
  unfold Lf at trans
  simp only [leftFactor_sameCollect T a L _hL] at trans
  let gPin : fold 𝒮 Zₐ (B₀ ∘ f) s = fold 𝒮 Zₐ B₀ v :=
    (std_fold_map B₀ f s).symm.trans (congrArg (fold 𝒮 Zₐ B₀) e)
  have H :
      eqToHom (congrArg (fold 𝒮 Zₐ G) d₂) ≫ rowsChart G P₀ v ≫
        act 𝒮 Zₐ (fun j => F.collect (B x) (P₀ j) ≫ T.map (𝟙 a) (p j)) v ≫ F.collect B₀ v ≫ T.map (𝟙 a) q =
      rowsChart G (P₀ ∘ f) s ≫
        act 𝒮 Zₐ (fun j => F.collect (B x) (P₀ (f j)) ≫ T.map (𝟙 a) (p (f j))) s ≫
        F.collect (B₀ ∘ f) s ≫ T.map (𝟙 a) (eqToHom gPin ≫ q) := trans
  rw [← eqToHom_trans (congrArg (fold 𝒮 Zₐ G) d₁) (congrArg (fold 𝒮 Zₐ G) d₂)]
  simp only [Category.assoc]
  rw [H]
  let b := fun (v : IntermediateChild (vs:=vs) y) => B' y v.val
  let Q' := P₀ ∘ f
  let W₀ := B₀ ∘ f
  let bpin (j : IntermediateChild (vs:=vs) y) : W₀ j = b j :=
    congrArg (B' y) (localContinuationIndex_read (hD x hx) j)
  let bp := congrArg (fun Z => fold 𝒮 Zₐ Z s) (funext bpin)
  let z := fun j => eqToHom (congrArg (fold 𝒮 Zₐ G) (eqQ j))
  let moved := fun j => F.collect (B x) (Q' j) ≫ T.map (𝟙 a) (p (f j))
  let pres := fun j => z j ≫ moved j
  let pUpdate := fun j => eqToHom (congrArg (T.obj a) (bpin j))
  let bStage := secondChildCell E t (List.getElem_mem _) y₀
  have partition := rowsChart_rows_congr G eqQ s
  have partition' : rowsChart G Q s ≫ act 𝒮 Zₐ z s =
    eqToHom (congrArg (fold 𝒮 Zₐ G) d₁) ≫ rowsChart G Q' s := partition
  rw [← reassoc_of% partition']
  have c : act 𝒮 Zₐ z s ≫ act 𝒮 Zₐ moved s = act 𝒮 Zₐ pres s :=
    act_seq (S:=𝒮) (Z:=Zₐ) z moved s
  have j0 : eqToHom gPin ≫ q = eqToHom bp ≫ bStage := by
    unfold bStage secondChildCell OrderedDependentMap.locInner q
    simp only [eqToHom_refl, Category.comp_id, eqToHom_trans_assoc]
    rfl
  have j1 : T.map (𝟙 a) (eqToHom bp ≫ bStage) =
    eqToHom (congrArg F.obj bp) ≫ T.map (𝟙 a) bStage := by
    have Z {u v : C} (e : u = v) : T.map (𝟙 a) (eqToHom e) = eqToHom (congrArg F.obj e) := by
      cases e
      exact T.map_id _ _
    have Y := T.map_seq (𝟙 a) (𝟙 a) (eqToHom bp) bStage
    change T.map (𝟙 a ≫ 𝟙 a) (eqToHom bp ≫ bStage) =
      T.map (𝟙 a) (eqToHom bp) ≫ T.map (𝟙 a) bStage at Y
    rw [Category.id_comp, Z] at Y
    exact Y
  change AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q s ≫
      act 𝒮 Zₐ z s ≫ act 𝒮 Zₐ moved s ≫ F.collect W₀ s ≫
        T.map (𝟙 a) (eqToHom gPin ≫ q) = _
  rw [reassoc_of% c, j0, j1]
  have k := collect_act_transport F bpin s
  change F.collect W₀ s ≫ eqToHom (congrArg F.obj bp) = act 𝒮 Zₐ pUpdate s ≫ F.collect b s at k
  rw [reassoc_of% k]
  have j2 : act 𝒮 Zₐ pres s ≫ act 𝒮 Zₐ pUpdate s =
      act 𝒮 Zₐ (fun j => pres j ≫ pUpdate j) s :=
    act_seq (S:=𝒮) (Z:=Zₐ) pres pUpdate s
  rw [reassoc_of% j2]
  have point (j : IntermediateChild (vs:=vs) y) :
      pres j ≫ pUpdate j = attachedSliceChildCell D L x₀ j.val j.property := by
    let v₀ := (vs y)[f j]
    let h₀ : v₀ ∈ vs y := List.getElem_mem _
    let rr := (localContinuationIndex_read (hD x hx) j).symm
    have ee {i j : V} (e : i = j) (hi : i ∈ vs y) (hj : j ∈ vs y) :
      eqToHom (congrArg (fun i => fold 𝒮 Zₐ G (childFibreA us D.child i x)) e) ≫
        (F.collect (B x) (childFibreA us D.child j x) ≫ T.map (𝟙 a) (D.inner x hx j hj)) ≫
        eqToHom (congrArg (fun i => T.obj a (B' y i)) e.symm) =
      F.collect (B x) (childFibreA us D.child i x) ≫ T.map (𝟙 a) (D.inner x hx i hi) := by
      cases e
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have M := ee rr j.property h₀
    change pres j ≫ pUpdate j =
      F.collect (B x) (Q j) ≫ T.map (𝟙 a) (OrderedDependentMap.innerSliceCell D x₀ j.val j.property)
    unfold pres z moved pUpdate OrderedDependentMap.innerSliceCell OrderedDependentMap.locInner
    simp only [Category.assoc, eqToHom_refl, Category.comp_id, Category.id_comp, eqToHom_trans_assoc] at M ⊢
    exact M
  rw [show (fun j => pres j ≫ pUpdate j) =
    (fun (j : IntermediateChild (vs:=vs) y) => attachedSliceChildCell D L x₀ j.val j.property) from funext point]

end DirectChildRow

section DirectParentRows
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

noncomputable def localParentIndex (hn : ys.Nodup) {z : Z} (y : E.Slice z) : Fin ys.length :=
  (wordPositions ys hn).symm ⟨y.val,y.property.1⟩

omit [DecidableEq Y] [DecidableEq V] in
theorem localParentIndex_read (hn : ys.Nodup) {z : Z} (y : E.Slice z) :
    ys[localParentIndex E hn y] = y.val :=
  congrArg Subtype.val ((wordPositions ys hn).apply_symm_apply ⟨y.val,y.property.1⟩)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] [DecidableEq V] in
theorem localParentRow_index (hn : ys.Nodup) (hm : zs.Nodup) (k : Fin zs.length) :
    (E.slice zs[k]).map (localParentIndex E hn) =
      fibreList (wordCarrier E.parent E.parent_mem hm) k := by
  let f := fun i : Fin ys.length => ys[i]
  have hf : Function.Injective f := fun i j e => Fin.ext (hn.getElem_inj.mp e)
  apply (List.map_inj_right (f:=f) (fun _ _ e => hf e)).mp
  rw [List.map_map]
  have e : f ∘ (localParentIndex E hn (z:=zs[k])) = Subtype.val :=
    funext (localParentIndex_read E hn)
  rw [e]
  exact (sliceWord_map ys E.parent zs[k]).trans ((wordCarrier_fibre E.parent E.parent_mem hm k).symm)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem directParentRows_position
    (hxs : xs.Nodup) (hn : ys.Nodup) (hm : zs.Nodup)
    (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
    (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)
    (b : C) [(rightFactor (T:=T) b).LaxBraided] (_hR : SameRightGather R b)
    (k : Fin zs.length)
    (r : AddressOrder X (parentFibreA xs (E.parent ∘ D.parent) zs[k])
      ((E.slice zs[k]).flatMap (fun y => parentFibreA xs D.parent y.val))) :
    let s := E.slice zs[k]
    let Q := fun y : E.Slice zs[k] => parentFibreA xs D.parent y.val
    let G := fun x => T.obj (A x) b
    DependentFibre.gather R A b (parentFibreA xs (E.parent ∘ D.parent) zs[k]) ≫
      T.map ((D.compose E hn hm hD hE).outer zs[k] (List.getElem_mem _)) (𝟙 b) =
    AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q s ≫
      act 𝒮 Zₐ (fun y => DependentFibre.gather R A b (Q y) ≫ T.map (D.outer y.val y.property.1) (𝟙 b)) s ≫
      DependentFibre.gather R (E.parentVal zs[k]) b s ≫ T.map (E.locOuter zs[k] (List.getElem_mem _)) (𝟙 b) := by
  intro s Q G
  let Ff := rightFactor (T:=T) b
  let F := linearFunctor Ff
  let f := localParentIndex E hn (z:=zs[k])
  let g := wordCarrier E.parent E.parent_mem hm
  let v := fibreList g k
  let B₀ := fun j : Fin ys.length => A' ys[j]
  let P₀ := fun j : Fin ys.length => parentFibreA xs D.parent ys[j]
  let p := fun j : Fin ys.length => D.outer ys[j] (List.getElem_mem _)
  let q := eqToHom (wordCarrier_fibre_pin E.parent E.parent_mem hm A' k) ≫ E.outer zs[k] (List.getElem_mem _)
  have e : s.map f = v := localParentRow_index E hn hm k
  have eqQ (y : E.Slice zs[k]) : Q y = P₀ (f y) :=
    congrArg (parentFibreA xs D.parent) (localParentIndex_read E hn y).symm
  let d₁ : s.flatMap Q = s.flatMap (P₀ ∘ f) := congrArg (fun h => s.flatMap h) (funext eqQ)
  let d₂ : s.flatMap (P₀ ∘ f) = v.flatMap P₀ :=
    (List.flatMap_map f P₀ s).symm.trans (congrArg (fun s => s.flatMap P₀) e)
  let r₀ := r.seq (castOrder (d₁.trans d₂))
  have d := compositeParent_linear_read D E R hxs hn hm hD hE b _hR k r₀
  dsimp only at d
  rw [d]
  have rate : AddressOrder.mapSum additiveStructure G r₀ =
      AddressOrder.mapSum additiveStructure G r ≫ eqToHom (congrArg (fold 𝒮 Zₐ G) (d₁.trans d₂)) := by
    change AddressOrder.mapSum additiveStructure G r ≫
      AddressOrder.mapSum additiveStructure G (castOrder (d₁.trans d₂)) = _
    rw [castOrder_map]
  rw [rate]
  simp only [Category.assoc]
  have trans := linear_partition_read_indices Ff A B₀ P₀ f s e p q
  dsimp only at trans
  unfold Ff at trans
  simp only [rightFactor_sameCollect R _hR] at trans
  let gPin : fold 𝒮 Zₐ (B₀ ∘ f) s = fold 𝒮 Zₐ B₀ v :=
    (std_fold_map B₀ f s).symm.trans (congrArg (fold 𝒮 Zₐ B₀) e)
  have H :
      eqToHom (congrArg (fold 𝒮 Zₐ G) d₂) ≫ rowsChart G P₀ v ≫
        act 𝒮 Zₐ (fun j => DependentFibre.gather R A b (P₀ j) ≫ T.map (p j) (𝟙 b)) v ≫
          DependentFibre.gather R B₀ b v ≫ T.map q (𝟙 b) =
      rowsChart G (P₀ ∘ f) s ≫
        act 𝒮 Zₐ (fun j => DependentFibre.gather R A b (P₀ (f j)) ≫ T.map (p (f j)) (𝟙 b)) s ≫
        DependentFibre.gather R (B₀ ∘ f) b s ≫ T.map (eqToHom gPin ≫ q) (𝟙 b) := trans
  rw [← eqToHom_trans (congrArg (fold 𝒮 Zₐ G) d₁) (congrArg (fold 𝒮 Zₐ G) d₂)]
  simp only [Category.assoc]
  rw [H]
  let Q' := P₀ ∘ f
  let B'₀ := B₀ ∘ f
  let B₁ := E.parentVal zs[k]
  let bpin (j : E.Slice zs[k]) : B'₀ j = B₁ j := congrArg A' (localParentIndex_read E hn j)
  let bp := congrArg (fun Z => fold 𝒮 Zₐ Z s) (funext bpin)
  let z := fun j => eqToHom (congrArg (fold 𝒮 Zₐ G) (eqQ j))
  let moved := fun j => DependentFibre.gather R A b (Q' j) ≫ T.map (p (f j)) (𝟙 b)
  let pres := fun j => z j ≫ moved j
  let pUpdate := fun j => eqToHom (congrArg (fun c => T.obj c b) (bpin j))
  let o := E.locOuter zs[k] (List.getElem_mem _)
  have partition' : rowsChart G Q s ≫ act 𝒮 Zₐ z s =
    eqToHom (congrArg (fold 𝒮 Zₐ G) d₁) ≫ rowsChart G Q' s := rowsChart_rows_congr G eqQ s
  rw [← reassoc_of% partition']
  have c : act 𝒮 Zₐ z s ≫ act 𝒮 Zₐ moved s = act 𝒮 Zₐ pres s :=
    act_seq (S:=𝒮) (Z:=Zₐ) z moved s
  have j0 : eqToHom gPin ≫ q = eqToHom bp ≫ o := by
    unfold q o OrderedDependentMap.locOuter
    simp only [eqToHom_trans_assoc]
  have j1 : T.map (eqToHom bp ≫ o) (𝟙 b) =
      eqToHom (congrArg F.obj bp) ≫ T.map o (𝟙 b) := by
    have Z {u v : C} (e : u = v) : T.map (eqToHom e) (𝟙 b) = eqToHom (congrArg F.obj e) := by
      cases e
      exact T.map_id _ _
    have Y := bi_map_comp (T:=T) (eqToHom bp) o (𝟙 b) (𝟙 b)
    rw [Category.id_comp, Z] at Y
    exact Y.symm
  change AddressOrder.mapSum additiveStructure G r ≫ rowsChart G Q s ≫
      act 𝒮 Zₐ z s ≫ act 𝒮 Zₐ moved s ≫ DependentFibre.gather R B'₀ b s ≫
        T.map (eqToHom gPin ≫ q) (𝟙 b) = _
  rw [reassoc_of% c, j0, j1]
  have hGather := collect_act_transport F bpin s
  unfold F Ff at hGather
  simp only [rightFactor_sameCollect R _hR] at hGather
  change DependentFibre.gather R B'₀ b s ≫ eqToHom (congrArg F.obj bp) =
    act 𝒮 Zₐ pUpdate s ≫ DependentFibre.gather R B₁ b s at hGather
  rw [reassoc_of% hGather]
  have j2 : act 𝒮 Zₐ pres s ≫ act 𝒮 Zₐ pUpdate s =
      act 𝒮 Zₐ (fun j => pres j ≫ pUpdate j) s :=
    act_seq (S:=𝒮) (Z:=Zₐ) pres pUpdate s
  rw [reassoc_of% j2]
  have point (j : E.Slice zs[k]) :
      pres j ≫ pUpdate j = DependentFibre.gather R A b (Q j) ≫ T.map (D.outer j.val j.property.1) (𝟙 b) := by
    let y₀ := ys[f j]
    let h₀ : y₀ ∈ ys := List.getElem_mem _
    let rr := (localParentIndex_read E hn j).symm
    have ee {i j : Y} (e : i = j) (hi : i ∈ ys) (hj : j ∈ ys) :
      eqToHom (congrArg (fun i => fold 𝒮 Zₐ G (parentFibreA xs D.parent i)) e) ≫
        (DependentFibre.gather R A b (parentFibreA xs D.parent j) ≫ T.map (D.outer j hj) (𝟙 b)) ≫
        eqToHom (congrArg (fun i => T.obj (A' i) b) e.symm) =
      DependentFibre.gather R A b (parentFibreA xs D.parent i) ≫ T.map (D.outer i hi) (𝟙 b) := by
      cases e
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have M := ee rr j.property.1 h₀
    unfold pres z moved pUpdate
    simp only [Category.assoc] at M ⊢
    exact M
  rw [show (fun j => pres j ≫ pUpdate j) = _ from funext point]

end DirectParentRows

set_option backward.isDefEq.respectTransparency false in
/-- Moving a parent-order circuit past the attached opaque rows expands
each parent move to the move of its entire addressed continuation block. -/
theorem taggedRaggedRows_parent_order {X U Q : Type u} (A : Q → C) (B : X → C)
    (f : X → U → Q) (L : X → List U) {xs xs' : List X} (r : AddressOrder X xs xs')
    (p : ∀ x, fold 𝒮 Zₐ (A ∘ f x) (L x) ⟶ B x) :
    taggedRaggedRows A f L xs ≫ act 𝒮 Zₐ p xs ≫ AddressOrder.mapSum additiveStructure B r =
      AddressOrder.mapSum additiveStructure A (liftRows (fun i => (L i).map (f i)) r) ≫
        taggedRaggedRows A f L xs' ≫ act 𝒮 Zₐ p xs' := by
  let Q := fun i => (L i).map (f i)
  let G := fun i => fold 𝒮 Zₐ A (Q i)
  let H := fun i => fold 𝒮 Zₐ (A ∘ f i) (L i)
  let e := fun i => eqToHom (std_fold_map A (f i) (L i))
  let p' := fun i => e i ≫ p i
  have h : act 𝒮 Zₐ e xs ≫ act 𝒮 Zₐ p xs = act 𝒮 Zₐ p' xs :=
    act_seq (S:=𝒮) (Z:=Zₐ) e p xs
  have k : act 𝒮 Zₐ e xs' ≫ act 𝒮 Zₐ p xs' = act 𝒮 Zₐ p' xs' :=
    act_seq (S:=𝒮) (Z:=Zₐ) e p xs'
  have hj := rowsChart_liftRows A Q r
  have j := AddressOrder.natural additiveNaturality p' r
  change act 𝒮 Zₐ p' xs ≫ AddressOrder.mapSum additiveStructure B r =
    AddressOrder.mapSum additiveStructure G r ≫ act 𝒮 Zₐ p' xs' at j
  unfold taggedRaggedRows
  simp only [Category.assoc]
  change rowsChart A Q xs ≫ act 𝒮 Zₐ e xs ≫ act 𝒮 Zₐ p xs ≫ _ =
    AddressOrder.mapSum additiveStructure A (liftRows Q r) ≫ rowsChart A Q xs' ≫ act 𝒮 Zₐ e xs' ≫ act 𝒮 Zₐ p xs'
  rw [reassoc_of% h, j, reassoc_of% hj, k]

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_parent_groups {X U Q I : Type u} (A : Q → C) (B : X → C)
    (f : X → U → Q) (L : X → List U) (is : List I) (rows : I → List X)
    (p : ∀ x, fold 𝒮 Zₐ (A ∘ f x) (L x) ⟶ B x) :
    let M := fun i => (L i).map (f i)
    let s := is.flatMap rows
    let e : s.flatMap M = is.flatMap (fun i => (rows i).flatMap M) := List.flatMap_assoc
    taggedRaggedRows A f L s ≫ act 𝒮 Zₐ p s ≫ rowsChart B rows is =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫
        rowsChart A (fun i => (rows i).flatMap M) is ≫
        act 𝒮 Zₐ (fun i => taggedRaggedRows A f L (rows i) ≫ act 𝒮 Zₐ p (rows i)) is := by
  intro M s e
  let G := fun i => fold 𝒮 Zₐ A (M i)
  let k := fun i => eqToHom (std_fold_map A (f i) (L i))
  let p' := fun i => k i ≫ p i
  have a (s : List X) : act 𝒮 Zₐ k s ≫ act 𝒮 Zₐ p s = act 𝒮 Zₐ p' s :=
    act_seq (S:=𝒮) (Z:=Zₐ) k p s
  have n : act 𝒮 Zₐ p' s ≫ rowsChart B rows is =
      rowsChart G rows is ≫ act 𝒮 Zₐ (fun i => act 𝒮 Zₐ p' (rows i)) is :=
    rowsChart_natural rows p' is
  have j := rowsChart_iterated A M rows is
  have j' : rowsChart A M s ≫ rowsChart G rows is =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ rowsChart A (fun i => (rows i).flatMap M) is ≫
      act 𝒮 Zₐ (fun i => rowsChart A M (rows i)) is := by
    have c := congrArg (fun w => eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ w) j
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at c
    exact c
  unfold taggedRaggedRows
  simp only [Category.assoc]
  change rowsChart A M s ≫ act 𝒮 Zₐ k s ≫ act 𝒮 Zₐ p s ≫ rowsChart B rows is = _
  rw [reassoc_of% a s, n, ← Category.assoc (rowsChart A M s), j']
  have h : act 𝒮 Zₐ (fun i => rowsChart A M (rows i)) is ≫
      act 𝒮 Zₐ (fun i => act 𝒮 Zₐ p' (rows i)) is =
      act 𝒮 Zₐ (fun i => rowsChart A M (rows i) ≫ act 𝒮 Zₐ p' (rows i)) is :=
    act_seq (S:=𝒮) (Z:=Zₐ) (fun i => rowsChart A M (rows i)) (fun i => act 𝒮 Zₐ p' (rows i)) is
  simp only [Category.assoc]
  rw [h]
  congr 1
  congr 1
  apply congrArg (fun z => act 𝒮 Zₐ z is)
  funext i
  exact congrArg (fun z => rowsChart A M (rows i) ≫ z) (a (rows i)).symm

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
