module
public import ContextualComposition.NativeIndependentComposition
public import ContextualComposition.NativeBinaryAugmentedNaturality
@[expose] public section

/-! The occurrence-first horizontal arrow is literally the native
product of the two unary arrows in an order-preserving retag. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z t
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem wordFamily_read_eq {X : Type w} {Y : Type z} (A : Y → C) (f : X → Y)
    (xs : List X) (ys : List Y) (h : xs.map f = ys) :
    wordFamily (A ∘ f) xs = wordFamily A ys := by
  subst ys
  unfold wordFamily
  have H {n m : Nat} (e : n = m) (p : Fin n → C) (q : Fin m → C) (h : ∀ j, p j = q (Fin.cast e j)) :
      (Family.mk n p : Family C) = Family.mk m q := by
    subst m
    exact congrArg (Family.mk n) (funext h)
  exact H (List.length_map f).symm _ _ (fun j => congrArg A (List.getElem_map f).symm)

set_option backward.isDefEq.respectTransparency false in
theorem nativeHom_heq_of_positions {A B A' B' : Family C} (p : Hom ℙ A B) (q : Hom ℙ A' B')
    (es : A = A') (et : B = B')
    (h : ∀ i, Fin.cast (congrArg Family.n et) (p.addr i) = q.addr (Fin.cast (congrArg Family.n es) i))
    (hp : ∀ j, HEq (p.cell j) (q.cell (Fin.cast (congrArg Family.n et) j))) :
    HEq p q := by
  subst A'
  subst B'
  have e : p.addr = q.addr := funext h
  cases p with
  | mk f p =>
    cases q with
    | mk g q =>
      apply heq_of_eq
      apply native_hom_ext e p q
      intro j
      have k := heq_paste (congrArg (fun l => standardPushObj l A.val j) e) rfl (hp j)
      simp only [eqToHom_refl, Category.comp_id] at k
      exact k

set_option backward.isDefEq.respectTransparency false in
theorem readWordNativeMap_heq
    {X : Type w} {Y : Type z} {X' : Type t} {Y' : Type u}
    [DecidableEq Y] [DecidableEq Y']
    {xs : List X} {ys : List Y} {xs' : List X'} {ys' : List Y'}
    (A : X' → C) (B : Y' → C) (f : X → X') (g : Y → Y')
    (D : X → Y) (E : X' → Y') (fs : ∀ x ∈ xs, D x ∈ ys) (gs : ∀ x ∈ xs', E x ∈ ys')
    (h : ys.Nodup) (h' : ys'.Nodup)
    (he : xs.map f = xs') (ht : ys.map g = ys')
    (_coh : ∀ x ∈ xs, g (D x) = E (f x))
    (p : ∀ j : Fin ys.length, fold 𝒮 Zₐ (A ∘ f) (wordFibre xs D ys[j]) ⟶ B (g ys[j]))
    (q : ∀ j : Fin ys'.length, fold 𝒮 Zₐ A (wordFibre xs' E ys'[j]) ⟶ B ys'[j])
    (_hCell : ∀ j : Fin ys.length, HEq (p j)
      (q (Fin.cast ((List.length_map g).symm.trans (congrArg List.length ht)) j))) :
    HEq (wordNativeMap D fs h (A ∘ f) (B ∘ g) p) (wordNativeMap E gs h' A B q) := by
  let es := wordFamily_read_eq A f xs xs' he
  let et := wordFamily_read_eq B g ys ys' ht
  let eqs := (List.length_map f).symm.trans (congrArg List.length he)
  let eqt := (List.length_map g).symm.trans (congrArg List.length ht)
  let F := wordCarrier D fs h
  let G := wordCarrier E gs h'
  apply nativeHom_heq_of_positions _ _ es et
  · intro i
    change Fin.cast eqt (F i) = G (Fin.cast eqs i)
    apply Fin.ext
    apply h'.getElem_inj.mp
    have a := (retag_word_get g ys ht (F i)).symm
    have b := wordCarrier_get D fs h i
    have c := _coh xs[i] (List.getElem_mem _)
    have d := retag_word_get f xs he i
    have e := wordCarrier_get E gs h' (Fin.cast eqs i)
    exact a.trans ((congrArg g b).trans (c.trans ((congrArg E d).trans e.symm)))
  · intro j
    let a := wordCarrier_fibre_pin D fs h (A ∘ f) j
    let b := wordCarrier_fibre_pin E gs h' A (Fin.cast eqt j)
    change HEq (eqToHom a ≫ p j) (eqToHom b ≫ q (Fin.cast eqt j))
    exact (hom_source_pin_heq a _).trans ((_hCell j).trans (hom_source_pin_heq b _).symm)

set_option backward.isDefEq.respectTransparency false in
theorem nativeHom_comp_heq {A B D A' B' D' : Family C}
    (p : Hom ℙ A B) (q : Hom ℙ B D) (p' : Hom ℙ A' B') (q' : Hom ℙ B' D')
    (_a : A = A') (_b : B = B') (_d : D = D') (_hp : HEq p p') (_hq : HEq q q') :
    HEq (p.comp q) (p'.comp q') := by
  subst A'
  subst B'
  subst D'
  rw [eq_of_heq _hp, eq_of_heq _hq]


section ProductSeparate
variable {T : Bi (coeff (C:=C))}
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem separateProductFamily_eq
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    independentFamily T (wordFamily (dependentLabels (T:=T) V A) (dependentWord xs us))
      (wordFamily (dependentLabels (T:=T) P B) (dependentWord ys vs)) =
    wordFamily (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves :=
  wordFamily_read_eq (separateLeafLabels (T:=T) V P A B) _ _ _ (quadRead_word xs ys us vs)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
/-- Equality after the canonical family transports, not merely
equivalence of observed augmentations. The read retag is order-preserving. -/
theorem separateBinaryMap_product_heq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (h : (dependentWord xs' us').Nodup) (h' : (dependentWord ys' vs').Nodup)
    (hw : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup) :
    HEq (independentNativeWordMap T (origDependentWordMap D R L h) (origDependentWordMap E R L h') R L)
      (separateBinaryMap D E R L hw) := by
  let xw := dependentWord xs us
  let yw := dependentWord ys vs
  let xw' := dependentWord xs' us'
  let yw' := dependentWord ys' vs'
  let a := separateLeafLabels (T:=T) V P A B
  let b := separateLeafLabels (T:=T) V' P' A' B'
  let this := quadRead xw yw
  let that := quadRead xw' yw'
  let p := origDependentWordMap D R L h
  let q := origDependentWordMap E R L h'
  let X₀ := wordFamily (dependentLabels (T:=T) V A) xw
  let Y₀ := wordFamily (dependentLabels (T:=T) P B) yw
  let X₁ := wordFamily (dependentLabels (T:=T) V' A') xw'
  let Y₁ := wordFamily (dependentLabels (T:=T) P' B') yw'
  let s := independentWord X₀ Y₀
  let t := independentWord X₁ Y₁
  let w := (fourOccurrenceExpr xs' ys' us' vs').leaves
  let f := Prod.map p.addr q.addr
  let g := quadCarrierMap D.parent D.child E.parent E.child
  let pp := fun j : Fin t.length => independentWordCell T p q R L t[j]
  let qq := fun j : Fin w.length => separateBinaryCell D E R L w[j] (List.getElem_mem _)
  have e : s.map this = (fourOccurrenceExpr xs ys us vs).leaves := quadRead_word xs ys us vs
  have d : t.map that = w := quadRead_word xs' ys' us' vs'
  let ec := (List.length_map that).symm.trans (congrArg List.length d)
  have m (i : Fin xw.length × Fin yw.length) : that (f i) = g (this i) := by
    have hx := wordCarrier_get (origDepCarrier D) (origDepCarrier_support D) h i.1
    have hy := wordCarrier_get (origDepCarrier E) (origDepCarrier_support E) h' i.2
    exact congrArg pairQuad (congrArg₂ Prod.mk hx hy)
  have hc (i : Fin t.length) : HEq (pp i) (qq (Fin.cast ec i)) := by
    let z := t[i]
    let x := xw'[z.1]
    let y := yw'[z.2]
    have e : pairQuad (x,y) = w[Fin.cast ec i] := retag_word_get that t d i
    let hW : pairQuad (x,y) ∈ w := e.symm ▸ List.getElem_mem _
    have a := independentDependentCell_raw_heq D E R L h h' z
    have b := separateBinaryCell_raw_heq D E R L _hl _hr x y (List.getElem_mem _) (List.getElem_mem _) hW
    have c {i j : X' × U' × Y' × W'} (e : i = j) (hi : i ∈ w) (hj : j ∈ w) :
        HEq (separateBinaryCell D E R L i hi) (separateBinaryCell D E R L j hj) := by cases e; rfl
    exact a.trans (b.symm.trans (c e hW (List.getElem_mem _)))
  exact readWordNativeMap_heq a b this that f g (independent_word_support p q) (separateSupport D E)
    (independentWord_nodup X₁ Y₁) hw e d (fun i _ => m i) pp qq hc

end ProductSeparate

set_option backward.isDefEq.respectTransparency false in
theorem separateBinaryMap_ident {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X U Y W : Type u} [DecidableEq X] [DecidableEq U] [DecidableEq Y] [DecidableEq W]
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    (hx : xs.Nodup) (hy : ys.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup)
    (h : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    separateBinaryMap (OrderedDependentMap.identity xs us V A hx hu)
      (OrderedDependentMap.identity ys vs P B hy hv) R L h =
      Hom.ident (wordFamily (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves) := by
  have e := separateBinaryMap_product_heq (OrderedDependentMap.identity xs us V A hx hu)
    (OrderedDependentMap.identity ys vs P B hy hv) R L _hl _hr
    (dependentWord_nodup hx hu) (dependentWord_nodup hy hv) h
  rw [origDependentWordMap_ident xs us V A hx hu R L _hl _hr,
    origDependentWordMap_ident ys vs P B hy hv R L _hl _hr, independentNativeWordMap_ident R L _ _ _hl _hr] at e
  have f {a b : Family C} (e : a = b) : HEq (Hom.ident (S:=ℙ) a) (Hom.ident (S:=ℙ) b) := by cases e; rfl
  exact eq_of_heq (e.symm.trans (f (separateProductFamily_eq (T:=T) V P A B xs ys us vs)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4400000 in
theorem separateBinaryMap_comp {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {X U Y W X' U' Y' W' X'' U'' Y'' W'' : Type u}
    [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
    [DecidableEq X''] [DecidableEq U''] [DecidableEq Y''] [DecidableEq W'']
    {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
    {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
    {xs'' : List X''} {ys'' : List Y''} {us'' : X'' → List U''} {vs'' : Y'' → List W''}
    {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
    {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
    {V'' : X'' → C} {P'' : Y'' → C} {A'' : X'' → U'' → C} {B'' : Y'' → W'' → C}
    (D : OrderedDependentMap xs us xs' us' V A V' A')
    (E : OrderedDependentMap ys vs ys' vs' P B P' B')
    (D' : OrderedDependentMap xs' us' xs'' us'' V' A' V'' A'')
    (E' : OrderedDependentMap ys' vs' ys'' vs'' P' B' P'' B'')
    (hx : xs.Nodup) (hy : ys.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup)
    (hx' : xs'.Nodup) (hy' : ys'.Nodup) (hx'' : xs''.Nodup) (hy'' : ys''.Nodup)
    (hD : ∀ x ∈ xs, (us' (D.parent x)).Nodup) (hE : ∀ y ∈ ys, (vs' (E.parent y)).Nodup)
    (hD' : ∀ x ∈ xs', (us'' (D'.parent x)).Nodup) (hE' : ∀ y ∈ ys', (vs'' (E'.parent y)).Nodup)
    (ha : (dependentWord xs' us').Nodup) (hb : (dependentWord ys' vs').Nodup)
    (ha' : (dependentWord xs'' us'').Nodup) (hb' : (dependentWord ys'' vs'').Nodup)
    (h₁ : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (h₂ : (fourOccurrenceExpr xs'' ys'' us'' vs'').leaves.Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    separateBinaryMap (D.compose D' hx' hx'' hD hD') (E.compose E' hy' hy'' hE hE') R L h₂ =
      (separateBinaryMap D E R L h₁).comp (separateBinaryMap D' E' R L h₂) := by
  let D₀ := D.compose D' hx' hx'' hD hD'
  let E₀ := E.compose E' hy' hy'' hE hE'
  let p := origDependentWordMap D R L ha
  let q := origDependentWordMap E R L hb
  let p' := origDependentWordMap D' R L ha'
  let q' := origDependentWordMap E' R L hb'
  let sep := separateBinaryMap D E R L h₁
  let sep' := separateBinaryMap D' E' R L h₂
  let sep'' := separateBinaryMap D₀ E₀ R L h₂
  let r := independentNativeWordMap T p q R L
  let r' := independentNativeWordMap T p' q' R L
  have e₀ := separateProductFamily_eq (T:=T) V P A B xs ys us vs
  have e₁ := separateProductFamily_eq (T:=T) V' P' A' B' xs' ys' us' vs'
  have e₂ := separateProductFamily_eq (T:=T) V'' P'' A'' B'' xs'' ys'' us'' vs''
  have s₀ : HEq r sep := separateBinaryMap_product_heq D E R L _hl _hr ha hb h₁
  have s₁ : HEq r' sep' := separateBinaryMap_product_heq D' E' R L _hl _hr ha' hb' h₂
  have s₂ := separateBinaryMap_product_heq D₀ E₀ R L _hl _hr ha' hb' h₂
  have hd := origDependentWordMap_comp D D' hx' hx'' hD hD' R L hx hu ha ha' N NR NL _hl _hr
  have he := origDependentWordMap_comp E E' hy' hy'' hE hE' R L hy hv hb hb' N NR NL _hl _hr
  change origDependentWordMap D₀ R L ha' = p.comp p' at hd
  change origDependentWordMap E₀ R L hb' = q.comp q' at he
  rw [hd, he, independentNativeWordMap_comp R L N NR NL p q p' q' _hl _hr] at s₂
  exact eq_of_heq (s₂.symm.trans (nativeHom_comp_heq r r' sep sep' e₀ e₁ e₂ s₀ s₁))


theorem NativeFamilyIso.cancel_pre {A B D : Family C} (e : NativeFamilyIso A B)
    {p q : Hom ℙ B D} (h : e.hom.comp p = e.hom.comp q) : p = q := by
  have z := congrArg (e.inv.comp) h
  rw [← Hom.comp_assoc, ← Hom.comp_assoc, e.inv_hom, Hom.ident_comp, Hom.ident_comp] at z
  exact z

theorem NativeFamilyIso.square_identity {A B : Family C} (e : NativeFamilyIso A B)
    {p : Hom ℙ A A} {q : Hom ℙ B B} (h : p.comp e.hom = e.hom.comp q)
    (i : p = Hom.ident A) : q = Hom.ident B := by
  apply e.cancel_pre
  rw [← h, i, Hom.ident_comp, Hom.comp_ident]

theorem NativeFamilyIso.squares_composition {A B D A' B' D' : Family C}
    (e : NativeFamilyIso A A') (f : NativeFamilyIso B B') (g : NativeFamilyIso D D')
    {p : Hom ℙ A B} {p' : Hom ℙ B D} {p'' : Hom ℙ A D}
    {q : Hom ℙ A' B'} {q' : Hom ℙ B' D'} {q'' : Hom ℙ A' D'}
    (h : p.comp f.hom = e.hom.comp q)
    (h' : p'.comp g.hom = f.hom.comp q') (h'' : p''.comp g.hom = e.hom.comp q'')
    (c : p'' = p.comp p') : q'' = q.comp q' := by
  apply e.cancel_pre
  rw [← h'', c, Hom.comp_assoc, h', ← Hom.comp_assoc, h, Hom.comp_assoc]

noncomputable def binaryNativeFamilyIso {T : Bi (coeff (C:=C))} {I : C} (m : Middle T I)
    {X U Y W : Type u}
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    (mi : MiddleInv m) (hn : (fourOccurrenceExpr xs ys us vs).leaves.Nodup) :
    NativeFamilyIso
      (wordFamily (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves)
      (wordFamily (jointLeafLabels (T:=T) V P A B) (fourJointExpr xs ys us vs).leaves) :=
  let r := gridOrder (fourExchangeChart xs ys us vs)
  nativeReindexIso (wordEquiv r.perm hn)
    (wordComparisonCells _ _ r hn (binaryLeafIso V P A B m mi))

set_option backward.isDefEq.respectTransparency false in
theorem jointBinaryMap_ident {T : Bi (coeff (C:=C))} {I : C}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    (m : Middle T I) (mi : MiddleInv m) (_h : MedialLinear m R L) (_j : MedialInner m R L)
    {X U Y W : Type u} [DecidableEq X] [DecidableEq U] [DecidableEq Y] [DecidableEq W]
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    (hx : xs.Nodup) (hy : ys.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup)
    (h : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    jointBinaryMap (OrderedDependentMap.identity xs us V A hx hu)
      (OrderedDependentMap.identity ys vs P B hy hv) R L h =
      Hom.ident (wordFamily (jointLeafLabels (T:=T) V P A B) (fourJointExpr xs ys us vs).leaves) := by
  let D := OrderedDependentMap.identity xs us V A hx hu
  let E := OrderedDependentMap.identity ys vs P B hy hv
  let e := binaryNativeFamilyIso m V P A B xs ys us vs mi h
  let p := separateBinaryMap D E R L h
  let q := jointBinaryMap D E R L h
  have h₀ : p.comp e.hom = e.hom.comp q := actual_binary_native_square D E R L N NR NL m mi h h _h _j
  have h₁ := separateBinaryMap_ident R L V P A B xs ys us vs hx hy hu hv h _hl _hr
  exact e.square_identity h₀ h₁

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3300000 in
theorem jointBinaryMap_comp {T : Bi (coeff (C:=C))} {I : C}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    (m : Middle T I) (mi : MiddleInv m) (_h : MedialLinear m R L) (_j : MedialInner m R L)
    {X U Y W X' U' Y' W' X'' U'' Y'' W'' : Type u}
    [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
    [DecidableEq X''] [DecidableEq U''] [DecidableEq Y''] [DecidableEq W'']
    {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
    {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
    {xs'' : List X''} {ys'' : List Y''} {us'' : X'' → List U''} {vs'' : Y'' → List W''}
    {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
    {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
    {V'' : X'' → C} {P'' : Y'' → C} {A'' : X'' → U'' → C} {B'' : Y'' → W'' → C}
    (D : OrderedDependentMap xs us xs' us' V A V' A')
    (E : OrderedDependentMap ys vs ys' vs' P B P' B')
    (D' : OrderedDependentMap xs' us' xs'' us'' V' A' V'' A'')
    (E' : OrderedDependentMap ys' vs' ys'' vs'' P' B' P'' B'')
    (hx : xs.Nodup) (hy : ys.Nodup) (hu : ∀ x ∈ xs, (us x).Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup)
    (hx' : xs'.Nodup) (hy' : ys'.Nodup) (hx'' : xs''.Nodup) (hy'' : ys''.Nodup)
    (hD : ∀ x ∈ xs, (us' (D.parent x)).Nodup) (hE : ∀ y ∈ ys, (vs' (E.parent y)).Nodup)
    (hD' : ∀ x ∈ xs', (us'' (D'.parent x)).Nodup) (hE' : ∀ y ∈ ys', (vs'' (E'.parent y)).Nodup)
    (ha : (dependentWord xs' us').Nodup) (hb : (dependentWord ys' vs').Nodup)
    (ha' : (dependentWord xs'' us'').Nodup) (hb' : (dependentWord ys'' vs'').Nodup)
    (h₀ : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    (h₁ : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (h₂ : (fourOccurrenceExpr xs'' ys'' us'' vs'').leaves.Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    jointBinaryMap (D.compose D' hx' hx'' hD hD') (E.compose E' hy' hy'' hE hE') R L h₂ =
      (jointBinaryMap D E R L h₁).comp (jointBinaryMap D' E' R L h₂) := by
  let e := binaryNativeFamilyIso m V P A B xs ys us vs mi h₀
  let f := binaryNativeFamilyIso m V' P' A' B' xs' ys' us' vs' mi h₁
  let g := binaryNativeFamilyIso m V'' P'' A'' B'' xs'' ys'' us'' vs'' mi h₂
  let D₀ := D.compose D' hx' hx'' hD hD'
  let E₀ := E.compose E' hy' hy'' hE hE'
  have r₀ : (separateBinaryMap D E R L h₁).comp f.hom = e.hom.comp (jointBinaryMap D E R L h₁) :=
    actual_binary_native_square D E R L N NR NL m mi h₀ h₁ _h _j
  have r₁ : (separateBinaryMap D' E' R L h₂).comp g.hom = f.hom.comp (jointBinaryMap D' E' R L h₂) :=
    actual_binary_native_square D' E' R L N NR NL m mi h₁ h₂ _h _j
  have r₂ : (separateBinaryMap D₀ E₀ R L h₂).comp g.hom = e.hom.comp (jointBinaryMap D₀ E₀ R L h₂) :=
    actual_binary_native_square D₀ E₀ R L N NR NL m mi h₀ h₂ _h _j
  exact e.squares_composition f g r₀ r₁ r₂
    (separateBinaryMap_comp R L N NR NL D E D' E' hx hy hu hv hx' hy' hx'' hy''
      hD hE hD' hE' ha hb ha' hb' h₁ h₂ _hl _hr)

/-- A literal augmented square on two native identities has the actual
augmented identities horizontally, without an extra augmentation law. -/
theorem BinaryNativeAugSquare.horizontal_identity {I : C} {A A' : Aug ℙ I}
    {e : NativeAugmentedIso A A'}
    {p : Hom ℙ A.base A.base} {q : Hom ℙ A'.base A'.base}
    (s : BinaryNativeAugSquare e e p q)
    (hp : p = Hom.ident A.base) (hq : q = Hom.ident A'.base) :
    s.separate = AugHom.ident A ∧ s.joint = AugHom.ident A' :=
  ⟨AugHom.ext (s.separate_native.trans hp), AugHom.ext (s.joint_native.trans hq)⟩

/-- The actual augmented horizontals compose when their literal native
components do. This applies to the independently constructed original
binary squares, not to newly chosen maps on their endpoints. -/
theorem BinaryNativeAugSquare.horizontal_composition
    {I : C} {A B D A' B' D' : Aug ℙ I}
    {e : NativeAugmentedIso A A'} {f : NativeAugmentedIso B B'}
    {g : NativeAugmentedIso D D'}
    {p : Hom ℙ A.base B.base} {q : Hom ℙ A'.base B'.base}
    {p' : Hom ℙ B.base D.base} {q' : Hom ℙ B'.base D'.base}
    {r : Hom ℙ A.base D.base} {r' : Hom ℙ A'.base D'.base}
    (s : BinaryNativeAugSquare e f p q) (t : BinaryNativeAugSquare f g p' q')
    (u : BinaryNativeAugSquare e g r r') (h : r = p.comp p') (h' : r' = q.comp q') :
    u.separate = s.separate.comp t.separate ∧ u.joint = s.joint.comp t.joint := by
  constructor
  · apply AugHom.ext
    change u.separate.native = s.separate.native.comp t.separate.native
    rw [u.separate_native, s.separate_native, t.separate_native, h]
  · apply AugHom.ext
    change u.joint.native = s.joint.native.comp t.joint.native
    rw [u.joint_native, s.joint_native, t.joint_native, h']

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
