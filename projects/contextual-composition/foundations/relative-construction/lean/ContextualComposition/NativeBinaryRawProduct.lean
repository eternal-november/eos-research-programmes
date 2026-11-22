module
public import ContextualComposition.NativeBinaryTreeProduct
@[expose] public section

/-! Relabel actual rectangle rows without identifying repeated coefficients. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z t
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {X Y : Type w} {A B : Type z}

theorem gridOver_map {I : Type w} {X : Type z} {Y : Type t}
    (f : X → Y) (P : Y → GridExpr I) (xs : List X) :
    GridExpr.over P (xs.map f) = GridExpr.over (fun x => P (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, GridExpr.over, ih]

set_option backward.isDefEq.respectTransparency false in
theorem actFamily_heq {X : Type w} {A B A' B' : X → C} (hA : A = A') (hB : B = B')
    {p : ∀ x, A x ⟶ B x} {q : ∀ x, A' x ⟶ B' x} (h : ∀ x, HEq (p x) (q x))
    (xs : List X) : HEq (act 𝒮 Zₐ p xs) (act 𝒮 Zₐ q xs) := by
  subst A'
  subst B'
  have e : p = q := funext fun x => eq_of_heq (h x)
  subst q
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem actRetag_heq {X : Type w} {Y : Type z} {A B : Y → C}
    (f : X → Y) (p : ∀ y, A y ⟶ B y) (xs : List X) :
    HEq (act 𝒮 Zₐ (fun x => p (f x)) xs) (act 𝒮 Zₐ p (xs.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [act]
    exact structural_map_heq (S:=𝒮) rfl rfl (std_fold_map A f xs).symm
      (std_fold_map B f xs).symm HEq.rfl ih

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem rectPairExpr_retag (f : X → A) (g : Y → B) (xs : List X) (ys : List Y) :
    retagGrid (Prod.map f g) (rectPairExpr xs ys) = rectPairExpr (xs.map f) (ys.map g) := by
  unfold rectPairExpr
  simp only [retagGrid_over, gridOver_map, retagGrid, Prod.map_apply]

set_option backward.isDefEq.respectTransparency false in
theorem rectWordChart_map_heq (H : A × B → C) (f : X → A) (g : Y → B)
    (xs : List X) (ys : List Y) :
    HEq (rectWordChart (H ∘ Prod.map f g) xs ys) (rectWordChart H (xs.map f) (ys.map g)) := by
  let e := rectPairExpr xs ys
  let h := rectPairExpr_retag f g xs ys
  let r := retagGrid (Prod.map f g) e
  let q := rectPairExpr (xs.map f) (ys.map g)
  let F := fold 𝒮 Zₐ H
  let G := H ∘ Prod.map f g
  let F' := fold 𝒮 Zₐ G
  let evalH := GridExpr.eval (S:=𝒮) (Z:=Zₐ) H
  let evalG := GridExpr.eval (S:=𝒮) (Z:=Zₐ) G
  let b₁ := (rectPairExpr_eval H (xs.map f) (ys.map g)).symm
  let b₂ := (congrArg evalH h).symm
  let b₃ := retagGrid_eval H (Prod.map f g) e
  let b₄ := rectPairExpr_eval G xs ys
  let a₁ := (congrArg F (rectPairExpr_leaves (xs.map f) (ys.map g))).symm
  let a₂ := (congrArg (fun (p : GridExpr (A × B)) => F p.leaves) h).symm
  let a₃ := (congrArg F (retagGrid_leaves (Prod.map f g) e)).trans (std_fold_map H (Prod.map f g) e.leaves)
  let a₄ := congrArg F' (rectPairExpr_leaves xs ys)
  have d {I : Type z} (A : I → C) {e₁ e₂ : GridExpr I} (h : e₁ = e₂) :
      HEq (compressGrid A e₁) (compressGrid A e₂) := by cases h; rfl
  have h₀ := rectPairExpr_chart G xs ys
  have h₁ := rectPairExpr_chart H (xs.map f) (ys.map g)
  have h₂ := compressGrid_retag H (Prod.map f g) e
  have c₀ : HEq (compressGrid G e) (rectWordChart G xs ys) := heq_of_paste a₄ b₄ h₀
  have c₁ : HEq (compressGrid H q) (rectWordChart H (xs.map f) (ys.map g)) :=
    heq_of_paste a₁.symm b₁.symm h₁
  have c₂ : HEq (compressGrid H r) (compressGrid G e) := heq_of_paste a₃ b₃ h₂
  exact c₀.symm.trans (c₂.symm.trans ((d H h).trans c₁))

set_option backward.isDefEq.respectTransparency false in
theorem rightGather_map_heq {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (V : A → C) {b b' : C} (e : b = b')
    (f : X → A) (xs : List X) :
    HEq (DependentFibre.gather R (V ∘ f) b xs) (DependentFibre.gather R V b' (xs.map f)) := by
  subst b'
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [DependentFibre.gather]
    let a := V (f x)
    let d := (std_fold_map V f xs).symm
    let c := (std_fold_map (fun a => T.obj (V a) b) f xs).symm
    refine structural_seq_heq (K:=coeff (C:=C))
      (congrArg (fun t => (𝒮).obj (T.obj a b) t) c)
      (congrArg (fun t => (𝒮).obj (T.obj a b) (T.obj t b)) d)
      (congrArg (fun t => T.obj ((𝒮).obj a t) b) d) ?_ ?_
    · exact structural_map_heq (S:=𝒮) rfl rfl c (congrArg (fun t => T.obj t b) d) HEq.rfl ih
    · have k (v v' : C) (h : v = v') : HEq (R.cons a v b) (R.cons a v' b) := by subst v';rfl
      exact k _ _ d


set_option backward.isDefEq.respectTransparency false in
theorem rowGather_map_heq {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (V : A → C) (W : B → C)
    (f : X → A) (g : Y → B) (xs : List X) (ys : List Y) :
    HEq (rowGather R L (V ∘ f) (W ∘ g) xs ys)
      (rowGather R L V W (xs.map f) (ys.map g)) := by
  let b := fold 𝒮 Zₐ (W ∘ g) ys
  let b' := fold 𝒮 Zₐ W (ys.map g)
  let h := (std_fold_map W g ys).symm
  let q := fun a => Lin.collect (Lin.left L (V a)) W (ys.map g)
  let p := fun x => Lin.collect (Lin.left L (V (f x))) (W ∘ g) ys
  let D := fun a => fold 𝒮 Zₐ (fun b => T.obj (V a) (W b)) (ys.map g)
  let E := fun a => T.obj (V a) b'
  let u := fun a => (std_fold_map (fun j => T.obj (V a) (W j)) g ys).symm
  let v := fun a => congrArg (T.obj (V a)) h
  let d := (congrArg (fun U => fold 𝒮 Zₐ U xs) (funext fun x => u (f x))).trans (std_fold_map D f xs).symm
  let e := (congrArg (fun U => fold 𝒮 Zₐ U xs) (funext fun x => v (f x))).trans (std_fold_map E f xs).symm
  have z := congrArg₂ T.obj (std_fold_map V f xs).symm h
  have h₁ : HEq (act 𝒮 Zₐ p xs) (act 𝒮 Zₐ q (xs.map f)) := by
    refine (actFamily_heq (funext fun x => u (f x)) (funext fun x => v (f x))
      (fun x => linCollect_map_heq (Lin.left L (V (f x))) W g ys) xs).trans ?_
    exact actRetag_heq f q xs
  exact structural_seq_heq (K:=coeff (C:=C)) d e z h₁ (rightGather_map_heq R V h f xs)

set_option backward.isDefEq.respectTransparency false in
theorem rectangleGather_map_heq {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (V : A → C) (W : B → C)
    (f : X → A) (g : Y → B) (xs : List X) (ys : List Y) :
    let H := fun q : A × B => T.obj (V q.1) (W q.2)
    HEq (rectWordChart (H ∘ Prod.map f g) xs ys ≫ rowGather R L (V ∘ f) (W ∘ g) xs ys)
      (rectWordChart H (xs.map f) (ys.map g) ≫ rowGather R L V W (xs.map f) (ys.map g)) := by
  intro H
  have a : (xs.product ys).map (Prod.map f g) = (xs.map f).product (ys.map g) := by
    simp only [List.product, List.map_flatMap, List.flatMap_map, List.map_map]
    rfl
  let d := (std_fold_map H (Prod.map f g) (xs.product ys)).symm.trans
    (congrArg (fold 𝒮 Zₐ H) a)
  let E := fun a => fold 𝒮 Zₐ (fun b => T.obj (V a) (W b)) (ys.map g)
  let e := (congrArg (fun U => fold 𝒮 Zₐ U xs)
    (funext fun x => (std_fold_map (fun b => T.obj (V (f x)) (W b)) g ys).symm)).trans
      (std_fold_map E f xs).symm
  let z := congrArg₂ T.obj (std_fold_map V f xs).symm (std_fold_map W g ys).symm
  exact structural_seq_heq (K:=coeff (C:=C)) d e z
    (rectWordChart_map_heq H f g xs ys) (rowGather_map_heq R L V W f g xs ys)


set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_preserves_span {X Y : Type w} {X' Y' : Type z} [DecidableEq Y] [DecidableEq Y']
    (A : X' → C) (B : Y' → C) (f : X → X') (g : Y → Y')
    (s : List X) (s' : List X') (t : List Y) (t' : List Y')
    (F : X → Y) (G : X' → Y') (e : s.map f = s') (d : t.map g = t')
    (hs : s.Nodup) (hs' : s'.Nodup) (ht : t.Nodup) (ht' : t'.Nodup)
    (h : ∀ x ∈ s, F x ∈ t) (h' : ∀ x ∈ s', G x ∈ t')
    (m : ∀ i : Fin t.length, (wordFibre s F t[i]).map f =
      wordFibre s' G t'[Fin.cast ((List.length_map g).symm.trans (congrArg List.length d)) i])
    (p : ∀ i : Fin t.length, fold 𝒮 Zₐ (A ∘ f) (wordFibre s F t[i]) ⟶ B (g t[i]))
    (p' : ∀ i : Fin t'.length, fold 𝒮 Zₐ A (wordFibre s' G t'[i]) ⟶ B t'[i])
    (_k : ∀ i : Fin t.length, HEq (p i)
      (p' (Fin.cast ((List.length_map g).symm.trans (congrArg List.length d)) i)))
    {I : C} (α : fold 𝒮 Zₐ (A ∘ f) s ⟶ I) (α' : fold 𝒮 Zₐ A s' ⟶ I)
    (β : fold 𝒮 Zₐ (B ∘ g) t ⟶ I) (β' : fold 𝒮 Zₐ B t' ⟶ I)
    (_hα : HEq α α') (_hβ : HEq β β') :
    (wordNativeMap F h ht (A ∘ f) (B ∘ g) p).comp (wordAug (B ∘ g) t β).ε =
        (wordAug (A ∘ f) s α).ε ↔
      (wordNativeMap G h' ht' A B p').comp (wordAug B t' β').ε = (wordAug A s' α').ε := by
  let ec : t.length = t'.length := (List.length_map g).symm.trans (congrArg List.length d)
  let r := wordNativePartitionOrder F h ht
  let q := wordNativePartitionOrder G h' ht'
  rw [wordNativeMap_preserving_iff F h hs ht (A ∘ f) (B ∘ g) p r α β, wordNativeMap_preserving_iff G h' hs' ht' A B p' q α' β']
  let L := fun i : Fin t.length => wordFibre s F t[i]
  let K := fun i : Fin t'.length => wordFibre s' G t'[i]
  let U := fun i : Fin t.length => B (g t[i])
  let V := fun i : Fin t'.length => B t'[i]
  have eqt (i : Fin t.length) : g t[i] = t'[Fin.cast ec i] := by
    subst t'
    exact (List.getElem_map g).symm
  let Hd := fun i => congrArg B (eqt i)
  let o := finiteOutputPin ec U V Hd
  let a := (std_fold_map A f s).symm.trans (congrArg (fold 𝒮 Zₐ A) e)
  let b := (std_fold_map B g t).symm.trans (congrArg (fold 𝒮 Zₐ B) d)
  let Z := fun i => (std_fold_map A f (L i)).symm.trans (congrArg (fold 𝒮 Zₐ A) (m i))
  let px := fun i => eqToHom (Z i) ≫ p' (Fin.cast ec i) ≫ eqToHom (Hd i).symm
  have heqp (i : Fin t.length) : p i = px i := by
    have H := heq_paste (Z i) (Hd i) (_k i)
    have P := congrArg (fun x => x ≫ eqToHom (Hd i).symm) H
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at P
    exact P
  have hcut := finiteWordChart_span A f id s s' ec L K U V
    (fun i => (m i).trans (List.map_id _).symm) Hd
    (e.trans (List.map_id _).symm) (e.symm ▸ hs') r q p'
  dsimp only at hcut
  change AddressOrder.mapSum additiveStructure (A ∘ f) r ≫ rowsChart (A ∘ f) L (List.finRange t.length) ≫
      act 𝒮 Zₐ px (List.finRange t.length) ≫ eqToHom o =
    eqToHom a ≫ AddressOrder.mapSum additiveStructure A q ≫ rowsChart A K (List.finRange t'.length) ≫
      act 𝒮 Zₐ p' (List.finRange t'.length) at hcut
  have tβ : β = eqToHom b ≫ β' := by
    have H := heq_paste b rfl _hβ
    simpa only [eqToHom_refl, Category.comp_id] using H
  have tα : α = eqToHom a ≫ α' := by
    have H := heq_paste a rfl _hα
    simpa only [eqToHom_refl, Category.comp_id] using H
  have j :
      eqToHom (wordTotalPin (B ∘ g) t) ≫ eqToHom b =
        eqToHom o ≫ eqToHom (wordTotalPin B t') := by rw [eqToHom_trans, eqToHom_trans]
  rw [show p = px from funext heqp, tα, tβ, reassoc_of% j, reassoc_of% hcut]
  let z := eqToHom a
  let _ : IsIso z := inferInstanceAs (IsIso (eqToHom a))
  exact cancel_epi z


omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem map_product_word (f : X → A) (g : Y → B) (xs : List X) (ys : List Y) :
    (xs.product ys).map (Prod.map f g) = (xs.map f).product (ys.map g) := by
  simp only [List.product, List.map_flatMap, List.flatMap_map, List.map_map]
  rfl

def pairRead {X U Y W : Type u} (xw : List (X × U)) (yw : List (Y × W))
    (p : Fin xw.length × Fin yw.length) : (X × U) × (Y × W) :=
  (xw[p.1], yw[p.2])

def quadRead {X U Y W : Type u} (xw : List (X × U)) (yw : List (Y × W))
    (p : Fin xw.length × Fin yw.length) : X × U × Y × W :=
  pairQuad (pairRead xw yw p)

theorem quadRead_word {X U Y W : Type u} (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    ((List.finRange xw.length).product (List.finRange yw.length)).map (quadRead xw yw) =
      (fourOccurrenceExpr xs ys us vs).leaves := by
  intro xw yw
  unfold quadRead
  change List.map (pairQuad ∘ (Prod.map (fun i : Fin xw.length => xw[i]) (fun j : Fin yw.length => yw[j]))) _ = _
  rw [← List.map_map, map_product_word, finRange_get, finRange_get]
  exact nativeOccurrenceExpr_word_product xs ys us vs

section FiniteAddress
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')

set_option backward.isDefEq.respectTransparency false in
theorem quadRead_fibre
    (h : (dependentWord xs' us').Nodup) (h' : (dependentWord ys' vs').Nodup)
    (t : Fin (dependentWord xs' us').length × Fin (dependentWord ys' vs').length) :
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    let xw' := dependentWord xs' us'
    let yw' := dependentWord ys' vs'
    let f := wordCarrier (origDepCarrier D) (origDepCarrier_support D) h
    let g := wordCarrier (origDepCarrier E) (origDepCarrier_support E) h'
    (wordFibre ((List.finRange xw.length).product (List.finRange yw.length)) (Prod.map f g) t).map
      (quadRead xw yw) =
        wordFibre (fourOccurrenceExpr xs ys us vs).leaves
          (quadCarrierMap D.parent D.child E.parent E.child) (quadRead xw' yw' t) := by
  intro xw yw xw' yw' f g
  rw [product_word_fibre]
  change List.map (pairQuad ∘ Prod.map (fun i : Fin xw.length => xw[i]) (fun j : Fin yw.length => yw[j])) _ = _
  rw [← List.map_map, map_product_word]
  have fd := wordCarrier_fibre (origDepCarrier D) (origDepCarrier_support D) h t.1
  have fe := wordCarrier_fibre (origDepCarrier E) (origDepCarrier_support E) h' t.2
  change (wordFibre (List.finRange xw.length) f t.1).map (fun i : Fin xw.length => xw[i]) =
    wordFibre xw (origDepCarrier D) xw'[t.1] at fd
  change (wordFibre (List.finRange yw.length) g t.2).map (fun i : Fin yw.length => yw[i]) =
    wordFibre yw (origDepCarrier E) yw'[t.2] at fe
  rw [fd, fe]
  exact separate_raw_fibre_product D E (pairRead xw' yw' t)

end FiniteAddress

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem hom_source_pin_heq {a b c : C} (e : a = b) (p : b ⟶ c) :
    HEq (eqToHom e ≫ p) p := by
  cases e
  simp only [eqToHom_refl, Category.id_comp, heq_eq_eq]

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem hom_target_pin_heq {a b c : C} (e : b = c) (p : a ⟶ b) :
    HEq (p ≫ eqToHom e) p := by
  cases e
  simp only [eqToHom_refl, Category.comp_id, heq_eq_eq]

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem biMap_heq {T : Bi (coeff (C:=C))} {a b c d a' b' c' d' : C}
    (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
    {p : a ⟶ b} {q : c ⟶ d} {p' : a' ⟶ b'} {q' : c' ⟶ d'}
    (h : HEq p p') (i : HEq q q') : HEq (T.map p q) (T.map p' q') :=
  structural_map_heq (S:=T) ea eb ec ed h i

set_option backward.isDefEq.respectTransparency false in
theorem rectangleCell_map_heq {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (V : A → C) (W : B → C)
    (f : X → A) (g : Y → B) (xs : List X) (ys : List Y)
    {a b a' b' : C} (ta : a = a') (tb : b = b')
    {p : fold 𝒮 Zₐ (V ∘ f) xs ⟶ a} {q : fold 𝒮 Zₐ (W ∘ g) ys ⟶ b}
    {p' : fold 𝒮 Zₐ V (xs.map f) ⟶ a'} {q' : fold 𝒮 Zₐ W (ys.map g) ⟶ b'}
    (ep : HEq p p') (eq : HEq q q') :
    let H := fun z : A × B => T.obj (V z.1) (W z.2)
    HEq (rectWordChart (H ∘ Prod.map f g) xs ys ≫ rowGather R L (V ∘ f) (W ∘ g) xs ys ≫ T.map p q)
      (rectWordChart H (xs.map f) (ys.map g) ≫ rowGather R L V W (xs.map f) (ys.map g) ≫ T.map p' q') := by
  intro H
  let d := (std_fold_map H (Prod.map f g) (xs.product ys)).symm.trans
    (congrArg (fold 𝒮 Zₐ H) (map_product_word f g xs ys))
  let x := (std_fold_map V f xs).symm
  let y := (std_fold_map W g ys).symm
  have z := congrArg₂ T.obj x y
  have h := rectangleGather_map_heq R L V W f g xs ys
  have k := biMap_heq (T:=T) x ta y tb ep eq
  have m := structural_seq_heq (K:=coeff (C:=C)) d z (congrArg₂ T.obj ta tb) h k
  change HEq ((rectWordChart (H ∘ Prod.map f g) xs ys ≫ _) ≫ _) ((rectWordChart H (xs.map f) (ys.map g) ≫ _) ≫ _) at m
  simpa only [Category.assoc] using m


section LocalCells
variable {T : Bi (coeff (C:=C))}
variable {X U X' U' : Type u} [DecidableEq X'] [DecidableEq U']
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

def dependentSliceCell (t : X' × U') (h : t ∈ dependentWord xs' us') :
    fold 𝒮 Zₐ (dependentLabels (T:=T) (D.parentVal t.1) (D.childVal t.1))
      (dependentWord (D.slice t.1) (D.terms t.1 t.2)) ⟶ dependentLabels (T:=T) V' W' t :=
  let m := (dependentWord_mem xs' us' t).mp h
  let E := dependentExpr (D.slice t.1) (D.terms t.1 t.2)
  let A := dependentLabels (T:=T) (D.parentVal t.1) (D.childVal t.1)
  eqToHom (congrArg (fold 𝒮 Zₐ A) (dependentExpr_leaves _ _).symm) ≫
    compressGrid A E ≫ eqToHom (dependentExpr_eval (T:=T) _ _ _ _) ≫
    dep R (D.parentVal t.1) (indexInput (D.childVal t.1) (D.terms t.1 t.2)) L
      (D.slice t.1) (D.locInner t.1 t.2 m.2) (D.locOuter t.1 m.1)

set_option backward.isDefEq.respectTransparency false in
theorem origDependentCell_slice_heq (t : X' × U') (h : t ∈ dependentWord xs' us') :
    HEq (origDependentCell D R L t h) (dependentSliceCell D R L t h) := by
  simp only [origDependentCell, dependentSliceCell, localCellToGlobal]
  exact (hom_source_pin_heq _ _).trans (hom_source_pin_heq _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem origDependent_position_cell_heq (hn : (dependentWord xs' us').Nodup)
    (t : Fin (dependentWord xs' us').length) :
    HEq ((origDependentWordMap D R L hn).cell t)
      (dependentSliceCell D R L (dependentWord xs' us')[t] (List.getElem_mem _)) := by
  let p := wordCarrier_fibre_pin (origDepCarrier D) (origDepCarrier_support D) hn
    (dependentLabels (T:=T) V W) t
  change HEq (eqToHom p ≫ origDependentCell D R L _ _) _
  exact (hom_source_pin_heq p _).trans (origDependentCell_slice_heq D R L _ _)

theorem dependentSlice_word_raw (t : X' × U') :
    (dependentWord (D.slice t.1) (D.terms t.1 t.2)).map (dependentSliceRelabel D t.1) =
      wordFibre (dependentWord xs us) (origDepCarrier D) t := by
  have h := dependentSlice_word D t
  rw [dependentExpr_leaves] at h
  exact h

end LocalCells

set_option backward.isDefEq.respectTransparency false in
theorem rectangleCell_map_heq' {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (V : A → C) (W : B → C)
    (f : X → A) (g : Y → B) (xs : List X) (ys : List Y)
    {xs' : List A} {ys' : List B} (_ex : xs.map f = xs') (_ey : ys.map g = ys')
    {a b : C}
    {p : fold 𝒮 Zₐ (V ∘ f) xs ⟶ a} {q : fold 𝒮 Zₐ (W ∘ g) ys ⟶ b}
    {p' : fold 𝒮 Zₐ V xs' ⟶ a} {q' : fold 𝒮 Zₐ W ys' ⟶ b}
    (ep : HEq p p') (eq : HEq q q') :
    let H := fun z : A × B => T.obj (V z.1) (W z.2)
    HEq (rectWordChart (H ∘ Prod.map f g) xs ys ≫ rowGather R L (V ∘ f) (W ∘ g) xs ys ≫ T.map p q)
      (rectWordChart H xs' ys' ≫ rowGather R L V W xs' ys' ≫ T.map p' q') := by
  subst xs'
  subst ys'
  exact rectangleCell_map_heq R L V W f g xs ys rfl rfl ep eq


section BinaryCells
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

def rawDependentPairCell (s : X' × U') (t : Y' × W')
    (hs : s ∈ dependentWord xs' us') (ht : t ∈ dependentWord ys' vs') :
    let xw := wordFibre (dependentWord xs us) (origDepCarrier D) s
    let yw := wordFibre (dependentWord ys vs) (origDepCarrier E) t
    let F := fun z : (X × U) × (Y × W) =>
      T.obj (dependentLabels (T:=T) V A z.1) (dependentLabels (T:=T) P B z.2)
    fold 𝒮 Zₐ F (xw.product yw) ⟶
      T.obj (dependentLabels (T:=T) V' A' s) (dependentLabels (T:=T) P' B' t) :=
  rectWordChart _ _ _ ≫ rowGather R L _ _ _ _ ≫
    T.map (origDependentCell D R L s hs) (origDependentCell E R L t ht)

set_option backward.isDefEq.respectTransparency false in
theorem separateBinaryCell_raw_heq
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (s : X' × U') (t : Y' × W') (hs : s ∈ dependentWord xs' us') (ht : t ∈ dependentWord ys' vs')
    (h : pairQuad (s,t) ∈ (fourOccurrenceExpr xs' ys' us' vs').leaves) :
    HEq (separateBinaryCell D E R L (pairQuad (s,t)) h) (rawDependentPairCell D E R L s t hs ht) := by
  let m := (dependentWord_mem xs' us' s).mp hs
  let n := (dependentWord_mem ys' vs' t).mp ht
  let ls := D.slice s.1
  let lt := E.slice t.1
  let lu := D.terms s.1 s.2
  let lv := E.terms t.1 t.2
  let ld := D.parentVal s.1
  let le := E.parentVal t.1
  let lk := D.childVal s.1
  let ll := E.childVal t.1
  let _ : ∀ p : D.Slice s.1 × U, (leftFactor T (dependentLabels (T:=T) ld lk p)).LaxBraided :=
    fun p => lF _
  let _ := rF (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) le ll) (dependentExpr lt lv))
  have q := separateWordCell_pair R L ld le lk ll ls lt lu lv (fun p => _hl _) (_hr _)
    (D.locInner s.1 s.2 m.2) (E.locInner t.1 t.2 n.2) (D.locOuter s.1 m.1) (E.locOuter t.1 n.1)
  dsimp only at q
  let l := separateWordCell ls lt lu lv ld le lk ll R L
    (D.locInner s.1 s.2 m.2) (E.locInner t.1 t.2 n.2) (D.locOuter s.1 m.1) (E.locOuter t.1 n.1)
  have k : HEq (separateBinaryCell D E R L (pairQuad (s,t)) h) l := by
    unfold separateBinaryCell localCellToGlobal
    exact hom_source_pin_heq _ _
  have hleft := (origDependentCell_slice_heq D R L s hs).symm
  have hright := (origDependentCell_slice_heq E R L t ht).symm
  have hrect := rectangleCell_map_heq' R L (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B)
    (dependentSliceRelabel D s.1) (dependentSliceRelabel E t.1)
    (dependentWord ls lu) (dependentWord lt lv)
    (dependentSlice_word_raw D s) (dependentSlice_word_raw E t) hleft hright
  have q' := (hom_source_pin_heq (occurrencePairPin (T:=T) ld le lk ll ls lt lu lv) l).symm
  have q'' := q'.trans (heq_of_eq q)
  exact k.trans (q''.trans hrect)


set_option backward.isDefEq.respectTransparency false in
theorem independentDependentCell_raw_heq
    (h : (dependentWord xs' us').Nodup) (h' : (dependentWord ys' vs').Nodup)
    (j : Fin (dependentWord xs' us').length × Fin (dependentWord ys' vs').length) :
    HEq (independentWordCell T (origDependentWordMap D R L h)
      (origDependentWordMap E R L h') R L j)
      (rawDependentPairCell D E R L (dependentWord xs' us')[j.1] (dependentWord ys' vs')[j.2]
        (List.getElem_mem _) (List.getElem_mem _)) := by
  let p := origDependentWordMap D R L h
  let q := origDependentWordMap E R L h'
  let f := fun i : Fin (dependentWord xs us).length => (dependentWord xs us)[i]
  let g := fun i : Fin (dependentWord ys vs).length => (dependentWord ys vs)[i]
  let s := (dependentWord xs' us')[j.1]
  let t := (dependentWord ys' vs')[j.2]
  have e : (fibreList p.addr j.1).map f = wordFibre (dependentWord xs us) (origDepCarrier D) s :=
    wordCarrier_fibre (origDepCarrier D) (origDepCarrier_support D) h j.1
  have e' : (fibreList q.addr j.2).map g = wordFibre (dependentWord ys vs) (origDepCarrier E) t :=
    wordCarrier_fibre (origDepCarrier E) (origDepCarrier_support E) h' j.2
  have ep := (origDependent_position_cell_heq D R L h j.1).trans
    (origDependentCell_slice_heq D R L s (List.getElem_mem _)).symm
  have eq := (origDependent_position_cell_heq E R L h' j.2).trans
    (origDependentCell_slice_heq E R L t (List.getElem_mem _)).symm
  have k := rectangleCell_map_heq' R L (dependentLabels (T:=T) V A) (dependentLabels (T:=T) P B)
    f g (fibreList p.addr j.1) (fibreList q.addr j.2) e e' ep eq
  dsimp only at k
  refine (hom_source_pin_heq _ _).trans k

end BinaryCells

set_option backward.isDefEq.respectTransparency false in
theorem independentDependentAugCell_heq {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X U Y W : Type u} (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    {I : C} (J : UnitCompat R I)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A us) x ⟶ I)
    (δ' : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B vs) y ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (ε' : fold 𝒮 Zₐ P ys ⟶ I) :
    let F := dependentLabels (T:=T) V A
    let G := dependentLabels (T:=T) P B
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    let a := eqToHom (wordTotalPin F xw) ≫ dependentWordAugCell R L J xs us V A δ ε
    let b := eqToHom (wordTotalPin G yw) ≫ dependentWordAugCell R L J ys vs P B δ' ε'
    HEq (independentWordAugCell T R L (wordFamily F xw) (wordFamily G yw) a b (J.ρ I))
      (separateWordAug xs ys us vs V P A B R L J δ δ' ε ε') := by
  intro F G xw yw a b
  let p := dependentWordAugCell R L J xs us V A δ ε
  let q := dependentWordAugCell R L J ys vs P B δ' ε'
  let f := fun i : Fin xw.length => xw[i]
  let g := fun i : Fin yw.length => yw[i]
  let H := fun z : (X × U) × (Y × W) => T.obj (F z.1) (G z.2)
  let _ : ∀ t : X × U, (leftFactor T (F t)).LaxBraided := fun t => lF _
  let _ := rF (GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (dependentExpr ys vs))
  have d := rectangleCell_map_heq' R L F G f g (List.finRange xw.length) (List.finRange yw.length)
    (finRange_get xw) (finRange_get yw)
    (show HEq a p from hom_source_pin_heq _ _) (show HEq b q from hom_source_pin_heq _ _)
  dsimp only at d
  have ea := quadRead_word xs ys us vs
  let e := ((std_fold_map (separateLeafLabels (T:=T) V P A B) (quadRead xw yw)
    ((List.finRange xw.length).product (List.finRange yw.length))).symm.trans
    (congrArg (fold 𝒮 Zₐ (separateLeafLabels (T:=T) V P A B)) ea)).trans
      (occurrencePairPin (T:=T) V P A B xs ys us vs).symm
  have d' := structural_seq_heq (K:=coeff (C:=C)) e rfl rfl d
    (show HEq (J.ρ I) (J.ρ I) from HEq.rfl)
  have h := separateWordAug_pair R L V P A B xs ys us vs (fun k => _hl _) (_hr _) J δ δ' ε ε'
  dsimp only at h
  change HEq ((_ ≫ _ ≫ T.map a b) ≫ J.ρ I) ((_ ≫ _ ≫ T.map p q) ≫ J.ρ I) at d'
  simp only [Category.assoc] at d'
  refine d'.trans ?_
  exact (heq_of_eq h.symm).trans (hom_source_pin_heq _ _)


theorem retag_word_get {X : Type w} {Y : Type z} (f : X → Y) (xs : List X) {ys : List Y}
    (h : xs.map f = ys) (i : Fin xs.length) :
    f xs[i] = ys[Fin.cast ((List.length_map f).symm.trans (congrArg List.length h)) i] := by
  subst ys
  exact (List.getElem_map f).symm

section Preserve
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
variable {I : C} (J : UnitCompat R I)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- The actual occurrence-first native arrow preserves the actual
occurrence-first augmentation. The hypotheses are the two already
independently defined unary preservation problems. -/
theorem separateBinary_preserves
    (N : GridBinary (symmetricCross (C:=C)) R L)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (hx : (dependentWord xs' us').Nodup) (hy : (dependentWord ys' vs').Nodup)
    (h₀ : (fourOccurrenceExpr xs ys us vs).leaves.Nodup)
    (h₁ : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A us) x ⟶ I)
    (η : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B vs) y ⟶ I)
    (δ' : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A' us') x ⟶ I)
    (η' : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B' vs') y ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (γ : fold 𝒮 Zₐ P ys ⟶ I)
    (ε' : fold 𝒮 Zₐ V' xs' ⟶ I) (γ' : fold 𝒮 Zₐ P' ys' ⟶ I)
    (hp : (origDependentWordMap D R L hx).comp (dependentWordAug R L J xs' us' V' A' δ' ε').ε =
      (dependentWordAug R L J xs us V A δ ε).ε)
    (hq : (origDependentWordMap E R L hy).comp (dependentWordAug R L J ys' vs' P' B' η' γ').ε =
      (dependentWordAug R L J ys vs P B η γ).ε) :
    (separateBinaryMap D E R L h₁).comp
      (wordAug (separateLeafLabels (T:=T) V' P' A' B') (fourOccurrenceExpr xs' ys' us' vs').leaves
        (separateWordAug xs' ys' us' vs' V' P' A' B' R L J δ' η' ε' γ')).ε =
      (wordAug (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves
        (separateWordAug xs ys us vs V P A B R L J δ η ε γ)).ε := by
  let F := dependentLabels (T:=T) V A
  let G := dependentLabels (T:=T) P B
  let F' := dependentLabels (T:=T) V' A'
  let G' := dependentLabels (T:=T) P' B'
  let xw := dependentWord xs us
  let yw := dependentWord ys vs
  let xw' := dependentWord xs' us'
  let yw' := dependentWord ys' vs'
  let X₀ := wordFamily F xw
  let Y₀ := wordFamily G yw
  let X₁ := wordFamily F' xw'
  let Y₁ := wordFamily G' yw'
  let p₀ := origDependentWordMap D R L hx
  let q₀ := origDependentWordMap E R L hy
  let a₀ := dependentWordAugCell R L J xs us V A δ ε
  let b₀ := dependentWordAugCell R L J ys vs P B η γ
  let a₁ := dependentWordAugCell R L J xs' us' V' A' δ' ε'
  let b₁ := dependentWordAugCell R L J ys' vs' P' B' η' γ'
  let a := eqToHom (wordTotalPin F xw) ≫ a₀
  let b := eqToHom (wordTotalPin G yw) ≫ b₀
  let a' := eqToHom (wordTotalPin F' xw') ≫ a₁
  let b' := eqToHom (wordTotalPin G' yw') ≫ b₁
  let p : AugHom ℙ (totalAug X₀ a) (totalAug X₁ a') := ⟨p₀, by
    change p₀.comp (totalAug X₁ a').ε = (totalAug X₀ a).ε
    rw [← wordAug_total_ε F' xw' a₁, ← wordAug_total_ε F xw a₀]
    exact hp⟩
  let q : AugHom ℙ (totalAug Y₀ b) (totalAug Y₁ b') := ⟨q₀, by
    change q₀.comp (totalAug Y₁ b').ε = (totalAug Y₀ b).ε
    rw [← wordAug_total_ε G' yw' b₁, ← wordAug_total_ε G yw b₀]
    exact hq⟩
  let _ : ∀ x : Fin X₀.n, (leftFactor T (X₀.val x)).LaxBraided := fun x => lF _
  let _ : (rightFactor (T:=T) (fold 𝒮 Zₐ Y₀.val ((List.finRange Y₁.n).flatMap (fibreList q.native.addr)))).LaxBraided := rF _
  let _ : (rightFactor (T:=T) (fold 𝒮 Zₐ (fun j => fold 𝒮 Zₐ Y₀.val (fibreList q.native.addr j))
    (List.finRange Y₁.n))).LaxBraided := rF _
  have H := (independentNativeAugMap T R L N NR NL p q (J.ρ I) (fun x => _hl _) (_hr _) (_hr _)).preserves
  let s := independentWord X₀ Y₀
  let t := independentWord X₁ Y₁
  let s' := (fourOccurrenceExpr xs ys us vs).leaves
  let t' := (fourOccurrenceExpr xs' ys' us' vs').leaves
  let f := quadRead xw yw
  let g := quadRead xw' yw'
  let A₀ := separateLeafLabels (T:=T) V P A B
  let A₁ := separateLeafLabels (T:=T) V' P' A' B'
  let K := Prod.map p₀.addr q₀.addr
  let K' := quadCarrierMap D.parent D.child E.parent E.child
  let e : s.map f = s' := quadRead_word xs ys us vs
  let d : t.map g = t' := quadRead_word xs' ys' us' vs'
  let ec : t.length = t'.length := (List.length_map g).symm.trans (congrArg List.length d)
  let C₀ := fun j : Fin t.length => independentWordCell T p₀ q₀ R L t[j]
  let C₁ := fun j : Fin t'.length => separateBinaryCell D E R L t'[j] (List.getElem_mem _)
  have bRead (i : Fin t.length) : g t[i] = t'[Fin.cast ec i] := retag_word_get g t d i
  have hf (i : Fin t.length) :
      (wordFibre s K t[i]).map f = wordFibre s' K' t'[Fin.cast ec i] :=
    (quadRead_fibre D E hx hy t[i]).trans (congrArg (wordFibre s' K') (bRead i))
  have hc (i : Fin t.length) : HEq (C₀ i) (C₁ (Fin.cast ec i)) := by
    let z : Fin X₁.n × Fin Y₁.n := t[i]
    let x := xw'[z.1]
    let y := yw'[z.2]
    let ex : x ∈ xw' := List.getElem_mem _
    let ey : y ∈ yw' := List.getElem_mem _
    have ez : pairQuad (x,y) = t'[Fin.cast ec i] := bRead i
    let h : pairQuad (x,y) ∈ t' := ez.symm ▸ (List.getElem_mem _)
    have H₀ := independentDependentCell_raw_heq D E R L hx hy z
    have H₁ := separateBinaryCell_raw_heq D E R L _hl _hr x y ex ey h
    have H₂ {j k : X' × U' × Y' × W'} (e : j = k) (hj : j ∈ t') (hk : k ∈ t') :
        HEq (separateBinaryCell D E R L j hj) (separateBinaryCell D E R L k hk) := by cases e; rfl
    exact H₀.trans (H₁.symm.trans (H₂ ez h (List.getElem_mem _)))
  let c₀ := independentWordAugCell T R L X₀ Y₀ a b (J.ρ I)
  let c₁ := independentWordAugCell T R L X₁ Y₁ a' b' (J.ρ I)
  let d₀ := separateWordAug xs ys us vs V P A B R L J δ η ε γ
  let d₁ := separateWordAug xs' ys' us' vs' V' P' A' B' R L J δ' η' ε' γ'
  have hsrc : HEq c₀ d₀ := independentDependentAugCell_heq R L V P A B xs ys us vs _hl _hr J δ η ε γ
  have hdst : HEq c₁ d₁ := independentDependentAugCell_heq R L V' P' A' B' xs' ys' us' vs' _hl _hr J δ' η' ε' γ'
  have result := wordNativeMap_preserves_span A₀ A₁ f g s s' t t' K K' e d
    (independentWord_nodup X₀ Y₀) h₀ (independentWord_nodup X₁ Y₁) h₁
    (independent_word_support p₀ q₀) (separateSupport D E) hf C₀ C₁ hc c₀ d₀ c₁ d₁ hsrc hdst
  exact result.mp H

end Preserve
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
