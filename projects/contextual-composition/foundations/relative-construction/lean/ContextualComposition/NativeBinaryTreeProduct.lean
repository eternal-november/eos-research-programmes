module
public import ContextualComposition.NativeDependentParentSquare

@[expose] public section
/-! Flattening paired additive charts without changing the original
multiplicative affine operation or the raw occurrence order. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X : Type w} {Y : Type z}

def graftGrid (P : X → GridExpr Y) : GridExpr X → GridExpr Y
  | .zero => .zero
  | .leaf x => P x
  | .bin v w => .bin (graftGrid P v) (graftGrid P w)

theorem graftGrid_leaves (P : X → GridExpr Y) (e : GridExpr X) :
    (graftGrid P e).leaves = e.leaves.flatMap (fun x => (P x).leaves) := by
  induction e with
  | zero => rfl
  | leaf x => exact (List.append_nil _).symm
  | bin v w ih ih' => simp only [graftGrid, GridExpr.leaves, List.flatMap_append, ih, ih']

theorem graftGrid_eval (A : Y → C) (P : X → GridExpr Y) (e : GridExpr X) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (graftGrid P e) =
      GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)) e := by
  induction e with
  | zero => rfl
  | leaf x => rfl
  | bin v w ih ih' => simp only [graftGrid, GridExpr.eval, ih, ih']

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_graft (A : Y → C) (P : X → GridExpr Y) (e : GridExpr X) :
    let L := fun x => (P x).leaves
    let B := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)
    compressGrid A (graftGrid P e) ≫ eqToHom (graftGrid_eval A P e) =
      eqToHom (congrArg (fold 𝒮 Zₐ A) (graftGrid_leaves P e)) ≫
      rowsChart A L e.leaves ≫ act 𝒮 Zₐ (fun x => compressGrid A (P x)) e.leaves ≫ compressGrid B e := by
  intro L B
  let F := fold 𝒮 Zₐ A
  let D := fun x => F (L x)
  let p := fun x => compressGrid A (P x)
  induction e with
  | zero =>
    change (𝟙 Zₐ) ≫ 𝟙 Zₐ = (𝟙 Zₐ) ≫ 𝟙 Zₐ ≫ 𝟙 Zₐ ≫ 𝟙 Zₐ
    simp only [Category.id_comp]
  | leaf x =>
    have m := rowsChart_one A L x
    let d : F (L x) = F (L x ++ []) := congrArg F (List.append_nil (L x)).symm
    change p x ≫ 𝟙 _ = eqToHom d ≫ rowsChart A L [x] ≫ (p x ⊗ₘ 𝟙 Zₐ) ≫ (ρ_ (B x)).hom
    have h : (p x ⊗ₘ 𝟙 Zₐ) ≫ (ρ_ (B x)).hom = (ρ_ (D x)).hom ≫ p x := by
      rw [tensorHom_id, rightUnitor_naturality]
    rw [h, reassoc_of% m, Category.comp_id]
  | bin l r ih ih' =>
    let a := l.leaves
    let b := r.leaves
    let U := (graftGrid P l).leaves
    let V := (graftGrid P r).leaves
    let ax := graftGrid_leaves P l
    let bx := graftGrid_leaves P r
    let i := graftGrid_eval A P l
    let j := graftGrid_eval A P r
    let H := congrArg₂ (fun u v : C => u ⊗ v) i j
    let K := congrArg F (congrArg₂ List.append ax bx)
    let W := congrArg F (List.flatMap_append (f:=L) (xs:=a) (ys:=b)).symm
    let p₁ := compressGrid A (graftGrid P l)
    let p₂ := compressGrid A (graftGrid P r)
    let q₁ := compressGrid B l
    let q₂ := compressGrid B r
    let r₁ := rowsChart A L a
    let r₂ := rowsChart A L b
    let u₁ := act 𝒮 Zₐ p a
    let u₂ := act 𝒮 Zₐ p b
    let s := join additiveStructure A U V
    let sa := join additiveStructure A (a.flatMap L) (b.flatMap L)
    let sb := join additiveStructure D a b
    let sc := join additiveStructure B a b
    have hCast {x x' y y' : C} (e : x = x') (f : y = y') :
        eqToHom (congrArg₂ (fun x y : C => x ⊗ y) e f) = eqToHom e ⊗ₘ eqToHom f := by
      cases e; cases f
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight]
    have jc {xs xs' ys ys' : List Y} (e : xs = xs') (j : ys = ys') :
        join additiveStructure A xs ys ≫ (eqToHom (congrArg F e) ⊗ₘ eqToHom (congrArg F j)) =
          eqToHom (congrArg F (congrArg₂ List.append e j)) ≫ join additiveStructure A xs' ys' := by
      cases e; cases j
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp]
      exact Category.comp_id _
    have ha : eqToHom W ≫ rowsChart A L (a ++ b) ≫ sb = sa ≫ (r₁ ⊗ₘ r₂) :=
      rowsChart_concat A L a b
    have hb : act 𝒮 Zₐ p (a ++ b) ≫ sc = sb ≫ (u₁ ⊗ₘ u₂) :=
      act_append additiveNaturality p a b
    have hc : p₁ ≫ eqToHom i = eqToHom (congrArg F ax) ≫ r₁ ≫ u₁ ≫ q₁ := ih
    have hd : p₂ ≫ eqToHom j = eqToHom (congrArg F bx) ≫ r₂ ≫ u₂ ≫ q₂ := ih'
    change (s ≫ (p₁ ⊗ₘ p₂)) ≫ eqToHom H =
      eqToHom (K.trans W) ≫ rowsChart A L (a ++ b) ≫ act 𝒮 Zₐ p (a ++ b) ≫ (sc ≫ (q₁ ⊗ₘ q₂))
    rw [hCast i j, Category.assoc, tensorHom_comp_tensorHom, hc, hd]
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
    rw [← eqToHom_trans K W]
    simp only [Category.assoc]
    rw [reassoc_of% jc ax bx, reassoc_of% hb, reassoc_of% ha]

variable {J : Type*}

theorem graftGrid_over (P : X → GridExpr Y) (Q : J → GridExpr X) (xs : List J) :
    graftGrid P (GridExpr.over Q xs) = GridExpr.over (fun x => graftGrid P (Q x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [GridExpr.over, graftGrid, ih]

theorem retagGrid_over (f : X → Y) (Q : J → GridExpr X) (xs : List J) :
    retagGrid f (GridExpr.over Q xs) = GridExpr.over (fun x => retagGrid f (Q x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [GridExpr.over, retagGrid, ih]

theorem graftGrid_product_leaves (e : GridExpr X) (f : GridExpr Y) :
    (graftGrid (fun x => retagGrid (Prod.mk x) f) e).leaves = e.leaves.product f.leaves := by
  rw [graftGrid_leaves, List.product]
  exact congrArg (fun L => e.leaves.flatMap L) (funext fun x => retagGrid_leaves (Prod.mk x) f)

variable {A B D E : Type u}

/-- The raw tree product, tagged directly with the original four-level addresses. -/
theorem nativeOccurrenceExpr_graft (xs : List A) (ys : List D) (us : A → List B) (vs : D → List E) :
    graftGrid (fun p : A × B =>
      retagGrid (fun q : D × E => (p.1,p.2,q.1,q.2)) (dependentExpr ys vs)) (dependentExpr xs us) =
      fourOccurrenceExpr xs ys us vs := by
  unfold dependentExpr fourOccurrenceExpr innerQuad
  rw [graftGrid_over]
  congr 1
  funext x
  rw [graftGrid_over]
  congr 1
  funext u
  simp only [graftGrid, retagGrid_over, retagGrid]

set_option backward.isDefEq.respectTransparency false in
/-- The recursively bracketed gather restricts to exactly the original
right-fold collector when the outer chart is a list of arbitrary subtrees. -/
theorem gatherE_over_collect (F : Lin 𝒮 Zₐ) (V : X → C) (P : J → GridExpr X) (xs : List J) :
    let E := GridExpr.eval (S:=𝒮) (Z:=Zₐ) V
    let G := fun i => F.obj (V i)
    eqToHom (GridExpr.eval_over G P xs).symm ≫ GridExpr.gatherE F V (GridExpr.over P xs) ≫
      eqToHom (congrArg F.obj (GridExpr.eval_over V P xs)) =
        act 𝒮 Zₐ (fun x => GridExpr.gatherE F V (P x)) xs ≫ Lin.collect F (E ∘ P) xs := by
  intro E G
  induction xs with
  | nil =>
    change (𝟙 _) ≫ F.nil ≫ 𝟙 _ = (𝟙 _) ≫ F.nil
    simp only [Category.comp_id]
  | cons a as ih =>
    let g := GridExpr.gatherE F V (P a)
    let h := GridExpr.gatherE F V (GridExpr.over P as)
    let p := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P as).symm
    let q := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V P as)
    let d := fun x => GridExpr.gatherE F V (P x)
    let b := fold 𝒮 Zₐ (E ∘ P) as
    let m := Lin.collect F (E ∘ P) as
    have c {x y z : C} (q : y = z) :
        eqToHom (congrArg (fun t => x ⊗ t) q) = 𝟙 x ⊗ₘ eqToHom q := by
      cases q
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight]
    change eqToHom p ≫ h ≫ eqToHom (congrArg F.obj q) = act 𝒮 Zₐ d as ≫ m at ih
    change eqToHom (congrArg (fun t => _ ⊗ t) p) ≫
      ((g ⊗ₘ h) ≫ F.cons (E (P a)) _) ≫ eqToHom (congrArg F.obj (congrArg (fun t => _ ⊗ t) q)) =
      (g ⊗ₘ act 𝒮 Zₐ d as) ≫ ((𝟙 _ ⊗ₘ m) ≫ F.cons (E (P a)) b)
    have move (x : C) {y z : C} (e : y = z) :
        (F.cons x y : F.obj x ⊗ F.obj y ⟶ F.obj (x ⊗ y)) ≫
          eqToHom (congrArg F.obj (congrArg (fun t => x ⊗ t) e)) =
        (𝟙 _ ⊗ₘ eqToHom (congrArg F.obj e)) ≫
          (F.cons x z : F.obj x ⊗ F.obj z ⟶ F.obj (x ⊗ z)) := by
      cases e
      simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rw [c (x := GridExpr.eval (S:=𝒮) (Z:=Zₐ) G (P a)) p, Category.assoc, move (E (P a)) q]
    have h₁ :
        (𝟙 _ ⊗ₘ eqToHom p) ≫ (g ⊗ₘ h) ≫ (𝟙 _ ⊗ₘ eqToHom (congrArg F.obj q)) =
          g ⊗ₘ (eqToHom p ≫ h ≫ eqToHom (congrArg F.obj q)) := by
      rw [tensorHom_comp_tensorHom, Category.comp_id, tensorHom_comp_tensorHom, Category.id_comp]
    have h₂ : (g ⊗ₘ act 𝒮 Zₐ d as) ≫ (𝟙 _ ⊗ₘ m) = g ⊗ₘ (act 𝒮 Zₐ d as ≫ m) := by
      rw [tensorHom_comp_tensorHom, Category.comp_id]
    rw [reassoc_of% h₁, reassoc_of% h₂, ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem gatherE_leaf_over_collect (F : Lin 𝒮 Zₐ) (V : X → C) (a : J → X) (xs : List J) :
    eqToHom (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) (fun x => F.obj (V x)) (fun j => .leaf (a j)) xs).symm ≫
      GridExpr.gatherE F V (GridExpr.over (fun j => .leaf (a j)) xs) ≫
      eqToHom (congrArg F.obj (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V (fun j => .leaf (a j)) xs)) =
      Lin.collect F (V ∘ a) xs := by
  have e := gatherE_over_collect F V (fun j => .leaf (a j)) xs
  have h : act 𝒮 Zₐ (fun j => 𝟙 (F.obj (V (a j)))) xs = 𝟙 _ := act_id_grid xs
  change _ = act 𝒮 Zₐ (fun j => 𝟙 (F.obj (V (a j)))) xs ≫ Lin.collect F (V ∘ a) xs at e
  rw [h, Category.id_comp] at e
  exact e


set_option backward.isDefEq.respectTransparency false in
theorem collect_act_transport (F : Lin 𝒮 Zₐ) {U V : J → C} (e : ∀ j, U j = V j) (xs : List J) :
    Lin.collect F U xs ≫ eqToHom (congrArg (fun A => F.obj (fold 𝒮 Zₐ A xs)) (funext e)) =
      act 𝒮 Zₐ (fun j => eqToHom (congrArg F.obj (e j))) xs ≫ Lin.collect F V xs := by
  have H := funext e
  cases H
  change Lin.collect F U xs ≫ 𝟙 _ = act 𝒮 Zₐ (fun j => 𝟙 (F.obj (U j))) xs ≫ Lin.collect F U xs
  rw [act_id_grid, Category.id_comp, Category.comp_id]


set_option backward.isDefEq.respectTransparency false in
theorem gatherE_over_nested_collect {I K : Type*} (F : Lin 𝒮 Zₐ)
    (V : X → C) (tag : I → K → X) (rows : I → List K) (xs : List I) :
    let P := fun i => GridExpr.over (fun k => .leaf (tag i k)) (rows i)
    let G := fun x => F.obj (V x)
    let p := fun i => GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G (fun k => .leaf (tag i k)) (rows i)
    let q := fun i => GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V (fun k => .leaf (tag i k)) (rows i)
    let a := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P xs).trans
      (congrArg (fun L => fold 𝒮 Zₐ L xs) (funext p))
    let b := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V P xs).trans
      (congrArg (fun L => fold 𝒮 Zₐ L xs) (funext q))
    eqToHom a.symm ≫ GridExpr.gatherE F V (GridExpr.over P xs) ≫ eqToHom (congrArg F.obj b) =
      act 𝒮 Zₐ (fun i => Lin.collect F (V ∘ tag i) (rows i)) xs ≫
        Lin.collect F (fun i => fold 𝒮 Zₐ (V ∘ tag i) (rows i)) xs := by
  intro P G p q a b
  let e := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P xs
  let d := GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V P xs
  let ep := congrArg (fun L => fold 𝒮 Zₐ L xs) (funext p)
  let dq := congrArg (fun L => F.obj (fold 𝒮 Zₐ L xs)) (funext q)
  let f := fun i => GridExpr.gatherE F V (P i)
  let m := fun i => Lin.collect F (V ∘ tag i) (rows i)
  have h := gatherE_over_collect F V P xs
  have g := collect_act_transport F q xs
  have k := std_act_eqToHom (fun i => (p i).symm) xs
  have ck : act 𝒮 Zₐ (fun i => eqToHom (p i).symm) xs = eqToHom ep.symm := k
  change eqToHom (ep.symm.trans e.symm) ≫ GridExpr.gatherE F V (GridExpr.over P xs) ≫
    eqToHom ((congrArg F.obj d).trans dq) = _
  rw [← eqToHom_trans ep.symm e.symm, ← eqToHom_trans (congrArg F.obj d) dq]
  simp only [Category.assoc]
  have h' : eqToHom e.symm ≫ GridExpr.gatherE F V (GridExpr.over P xs) ≫ eqToHom (congrArg F.obj d) =
    act 𝒮 Zₐ f xs ≫ Lin.collect F (fun j => GridExpr.eval (S:=𝒮) (Z:=Zₐ) V (P j)) xs := h
  rw [reassoc_of% h', g]
  rw [← ck]
  have comp₁ := act_seq (S:=𝒮) (Z:=Zₐ) (fun i => eqToHom (p i).symm) f xs
  have comp₂ := act_seq (S:=𝒮) (Z:=Zₐ)
    (fun i => eqToHom (p i).symm ≫ f i) (fun i => eqToHom (congrArg F.obj (q i))) xs
  change act 𝒮 Zₐ _ xs ≫ act 𝒮 Zₐ f xs = _ at comp₁
  change act 𝒮 Zₐ _ xs ≫ act 𝒮 Zₐ (fun i => eqToHom (congrArg F.obj (q i))) xs = _ at comp₂
  rw [reassoc_of% comp₁, reassoc_of% comp₂]
  congr 1
  exact congrArg (fun H => act 𝒮 Zₐ H xs) (funext fun i =>
    gatherE_leaf_over_collect F V (tag i) (rows i))


set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_act_transport {A B : X → C} (E : ∀ x, A x = B x) (e : GridExpr X) :
    compressGrid A e ≫ eqToHom (congrArg (fun H => GridExpr.eval (S:=𝒮) (Z:=Zₐ) H e) (funext E)) =
      act 𝒮 Zₐ (fun x => eqToHom (E x)) e.leaves ≫ compressGrid B e := by
  have H := funext E
  cases H
  change compressGrid A e ≫ 𝟙 _ = act 𝒮 Zₐ (fun x => 𝟙 (A x)) e.leaves ≫ compressGrid A e
  rw [act_id_grid, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The raw pair word and the literal product tree have the same additive
map after rowwise compression, even for a padded or empty subtree. -/
theorem compressGrid_product {X Y : Type u} (A : X × Y → C) (e : GridExpr X) (f : GridExpr Y) :
    let P := fun x => retagGrid (Prod.mk x) f
    let V := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun y => A (x,y)) f
    let h := (graftGrid_eval A P e).trans
      (congrArg (fun B => GridExpr.eval (S:=𝒮) (Z:=Zₐ) B e)
        (funext fun x => retagGrid_eval A (Prod.mk x) f))
    eqToHom (congrArg (fold 𝒮 Zₐ A) (graftGrid_product_leaves e f).symm) ≫
      compressGrid A (graftGrid P e) ≫ eqToHom h =
      rectWordChart A e.leaves f.leaves ≫
        act 𝒮 Zₐ (fun x => compressGrid (fun y => A (x,y)) f) e.leaves ≫ compressGrid V e := by
  intro P V h
  let U := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x)
  let L := fun x => (P x).leaves
  let M := fun (x : X) => f.leaves.map (Prod.mk x)
  let E := fun x => retagGrid_eval A (Prod.mk x) f
  let F := fold 𝒮 Zₐ A
  let r := fun (x : X) => retagGrid_leaves (Prod.mk x) f
  let p := fun x => compressGrid A (P x)
  let q := fun x => compressGrid (fun y => A (x,y)) f
  let xw := e.leaves
  let α := congrArg F (graftGrid_product_leaves e f).symm
  let β := congrArg F (graftGrid_leaves P e)
  let η : xw.flatMap L = xw.flatMap M := congrArg (fun N => xw.flatMap N) (funext r)
  let γ := congrArg (fun H => GridExpr.eval (S:=𝒮) (Z:=Zₐ) H e) (funext E)
  let d := fun x => congrArg F (r x)
  let j := fun x => std_fold_map A (Prod.mk x) f.leaves
  have hd : act 𝒮 Zₐ (fun x => eqToHom (d x)) xw = eqToHom
      (congrArg (fun H => fold 𝒮 Zₐ H xw) (funext d)) := std_act_eqToHom d xw
  have hn : compressGrid U e ≫ eqToHom γ =
      act 𝒮 Zₐ (fun x => eqToHom (E x)) xw ≫ compressGrid V e := compressGrid_act_transport E e
  have hG := compressGrid_graft A P e
  change compressGrid A (graftGrid P e) ≫ eqToHom (graftGrid_eval A P e) =
    eqToHom β ≫ rowsChart A L xw ≫ act 𝒮 Zₐ p xw ≫ compressGrid U e at hG
  change eqToHom α ≫ compressGrid A (graftGrid P e) ≫
    eqToHom ((graftGrid_eval A P e).trans γ) = _
  rw [← eqToHom_trans (graftGrid_eval A P e) γ, reassoc_of% hG, hn, ← Category.assoc (eqToHom α) (eqToHom β), eqToHom_trans α β]
  have c {J : Type u} {U V W : J → C} (p : ∀ i, U i ⟶ V i) (q : ∀ i, V i ⟶ W i) (xs : List J) :
      act 𝒮 Zₐ p xs ≫ act 𝒮 Zₐ q xs = act 𝒮 Zₐ (fun i => p i ≫ q i) xs :=
    act_seq (S:=𝒮) (Z:=Zₐ) p q xs
  let t : ∀ x, U x ⟶ V x := fun x => eqToHom (E x)
  have c₁ := c p t xw
  change eqToHom (α.trans β) ≫ rowsChart A L xw ≫ act 𝒮 Zₐ p xw ≫ act 𝒮 Zₐ t xw ≫ compressGrid V e = _
  rw [← Category.assoc (act 𝒮 Zₐ p xw), c₁]
  have hq : (fun x => p x ≫ eqToHom (E x)) = fun x => eqToHom (d x) ≫ eqToHom (j x) ≫ q x := by
    funext x
    rw [← Category.assoc (eqToHom (d x)), eqToHom_trans]
    exact compressGrid_retag A (Prod.mk x) f
  change (fun x => p x ≫ t x) = _ at hq
  rw [hq]
  have c₂ := c (fun x => eqToHom (d x)) (fun x => eqToHom (j x) ≫ q x) xw
  have c₃ := c (fun x => eqToHom (j x)) q xw
  rw [← c₂, Category.assoc, ← c₃, Category.assoc, hd]
  have hh : rowsChart A L xw ≫ eqToHom (congrArg (fun H => fold 𝒮 Zₐ H xw) (funext d)) =
      eqToHom (congrArg F η) ≫ rowsChart A M xw := (congrArg (fun k => rowsChart A L xw ≫ k) hd).symm.trans (rowsChart_rows_congr A r xw)
  rw [reassoc_of% hh, ← Category.assoc (eqToHom (α.trans β)), eqToHom_trans]
  change eqToHom _ ≫ _ = _
  have idh : (α.trans β).trans (congrArg F η) = rfl := Subsingleton.elim _ _
  rw [idh, eqToHom_refl, Category.id_comp]
  simp only [rectWordChart, Category.assoc]
  rfl


section Gather
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The flat rectangular gather and the independently computed nested
tree gather agree after their actual additive compression maps. -/
theorem productTreeGather_flat {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (A : X → C) (B : Y → C) (e : GridExpr X) (f : GridExpr Y)
    [∀ x, (leftFactor T (A x)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f)).LaxBraided]
    (_hl : ∀ x, SameLeftGather T (A x) L)
    (_hR : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f)) :
    let right := fun x => GridExpr.gatherE (linearFunctor (leftFactor T (A x))) B f
    let left := GridExpr.gatherE (linearFunctor (rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f))) A e
    let c := compressGrid B f
    let d := compressGrid A e
    rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) e.leaves f.leaves ≫
      act 𝒮 Zₐ (fun x => compressGrid (fun y => T.obj (A x) (B y)) f) e.leaves ≫
      compressGrid (fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun y => T.obj (A x) (B y)) f) e ≫
      GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e ≫ left =
    rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) e.leaves f.leaves ≫ rowGather R L A B e.leaves f.leaves ≫ T.map d c := by
  intro right left c d
  let b := GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f
  let b₀ := fold 𝒮 Zₐ B f.leaves
  let D := fun x => GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun y => T.obj (A x) (B y)) f
  let P := fun x => T.obj (A x) b
  let middle := fun x => compressGrid (fun y => T.obj (A x) (B y)) f
  let gatherRight := fun x => Lin.collect (Lin.left L (A x)) B f.leaves
  let h := fun x => T.map (𝟙 (A x)) c
  have r (x : X) : middle x ≫ right x = gatherRight x ≫ h x := by
    have q := collect_compressGrid (leftFactor T (A x)) B f
    rw [leftFactor_sameCollect T (A x) L (_hl x)] at q
    exact q
  have l : compressGrid P e ≫ left = DependentFibre.gather R A b e.leaves ≫ T.map d (𝟙 b) := by
    have q := collect_compressGrid (rightFactor (T:=T) b) A e
    rw [rightFactor_sameCollect R _hR] at q
    exact q
  have act_n := compressGrid_natural (A:=D) (B:=P) right e
  have act_c {U V W : X → C} (p : ∀ i, U i ⟶ V i) (q : ∀ i, V i ⟶ W i) :
      act 𝒮 Zₐ p e.leaves ≫ act 𝒮 Zₐ q e.leaves = act 𝒮 Zₐ (fun i => p i ≫ q i) e.leaves :=
    act_seq (S:=𝒮) (Z:=Zₐ) p q e.leaves
  have i := gather_nat R A c e.leaves
  have i' : DependentFibre.gather R A b₀ e.leaves ≫ T.map (𝟙 _) c =
      act 𝒮 Zₐ h e.leaves ≫ DependentFibre.gather R A b e.leaves := i
  have j : T.map (𝟙 _) c ≫ T.map d (𝟙 b) = T.map d c := by
    have q := T.map_seq (𝟙 (fold 𝒮 Zₐ A e.leaves)) d c (𝟙 b)
    change T.map (𝟙 _ ≫ d) (c ≫ 𝟙 b) = T.map (𝟙 _) c ≫ T.map d (𝟙 b) at q
    rw [Category.id_comp, Category.comp_id] at q
    exact q.symm
  change rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) e.leaves f.leaves ≫ act 𝒮 Zₐ middle e.leaves ≫ compressGrid D e ≫ GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e ≫ left =
    rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) e.leaves f.leaves ≫
      (act 𝒮 Zₐ gatherRight e.leaves ≫ DependentFibre.gather R A b₀ e.leaves) ≫ T.map d c
  rw [← reassoc_of% act_n, l, reassoc_of% act_c middle right]
  rw [show (fun x => middle x ≫ right x) = (fun x => gatherRight x ≫ h x) from funext r,
    ← reassoc_of% act_c gatherRight h, ← reassoc_of% i', j]
  simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
theorem graftedProduct_flatGather {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X Y : Type u} (A : X → C) (B : Y → C) (e : GridExpr X) (f : GridExpr Y)
    [∀ x, (leftFactor T (A x)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f)).LaxBraided]
    (_hl : ∀ x, SameLeftGather T (A x) L)
    (_hR : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f)) :
    let G := fun z : X × Y => T.obj (A z.1) (B z.2)
    let P := fun x => retagGrid (Prod.mk x) f
    let h := (graftGrid_eval G P e).trans
      (congrArg (fun H => GridExpr.eval (S:=𝒮) (Z:=Zₐ) H e)
        (funext fun x => retagGrid_eval G (Prod.mk x) f))
    let right := fun x => GridExpr.gatherE (linearFunctor (leftFactor T (A x))) B f
    let left := GridExpr.gatherE (linearFunctor (rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) B f))) A e
    eqToHom (congrArg (fold 𝒮 Zₐ G) (graftGrid_product_leaves e f).symm) ≫
      compressGrid G (graftGrid P e) ≫ eqToHom h ≫ GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e ≫ left =
      rectWordChart G e.leaves f.leaves ≫ rowGather R L A B e.leaves f.leaves ≫
        T.map (compressGrid A e) (compressGrid B f) := by
  intro G P h right left
  have q := compressGrid_product G e f
  dsimp only at q
  rw [reassoc_of% q]
  exact productTreeGather_flat R L A B e f _hl _hR

end Gather

theorem retagGrid_graft {Q : Type*} (h : Y → Q) (P : X → GridExpr Y) (e : GridExpr X) :
    retagGrid h (graftGrid P e) = graftGrid (fun x => retagGrid h (P x)) e := by
  induction e with
  | zero => rfl
  | leaf => rfl
  | bin l r ih ih' => simp only [retagGrid, graftGrid, ih, ih']

theorem retagGrid_retag {Q : Type*} (h : Y → Q) (g : X → Y) (e : GridExpr X) :
    retagGrid h (retagGrid g e) = retagGrid (h ∘ g) e := by
  induction e with
  | zero => rfl
  | leaf => rfl
  | bin l r ih ih' => simp only [retagGrid, ih, ih']

def pairQuad {A B D E : Type u} (p : (A × B) × (D × E)) : A × B × D × E :=
  (p.1.1,p.1.2,p.2.1,p.2.2)

theorem nativeOccurrenceExpr_retag_product {A B D E : Type u} (xs : List A) (ys : List D)
    (us : A → List B) (vs : D → List E) :
    retagGrid pairQuad
      (graftGrid (fun p => retagGrid (Prod.mk p) (dependentExpr ys vs)) (dependentExpr xs us)) =
      fourOccurrenceExpr xs ys us vs := by
  rw [retagGrid_graft]
  simp only [retagGrid_retag]
  exact nativeOccurrenceExpr_graft xs ys us vs

theorem nativeOccurrenceExpr_word_product {A B D E : Type u} (xs : List A) (ys : List D)
    (us : A → List B) (vs : D → List E) :
    ((dependentWord xs us).product (dependentWord ys vs)).map pairQuad =
      (fourOccurrenceExpr xs ys us vs).leaves := by
  rw [← dependentExpr_leaves, ← dependentExpr_leaves, ← graftGrid_product_leaves,
    ← retagGrid_leaves, nativeOccurrenceExpr_retag_product]


section PairAddress
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')

theorem pairQuad_injective {A B D E : Type u} :
    Function.Injective (pairQuad (A:=A) (B:=B) (D:=D) (E:=E)) := by
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨a',b'⟩,⟨c',d'⟩⟩ h
  cases h
  rfl

/-- Taking a raw target quadruple fibre is exactly taking both independent
raw dependent fibres. The equation includes empty and many-to-one fibres. -/
theorem separate_raw_fibre_product (t : (X' × U') × (Y' × W')) :
    ((wordFibre (dependentWord xs us) (origDepCarrier D) t.1).product
      (wordFibre (dependentWord ys vs) (origDepCarrier E) t.2)).map pairQuad =
      wordFibre (fourOccurrenceExpr xs ys us vs).leaves
        (quadCarrierMap D.parent D.child E.parent E.child) (pairQuad t) := by
  rw [← product_word_fibre, ← nativeOccurrenceExpr_word_product]
  unfold wordFibre
  rw [List.filter_map]
  apply congrArg (fun p => (((dependentWord xs us).product (dependentWord ys vs)).filter p).map pairQuad)
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact ⟨fun e => congrArg pairQuad e, fun e => pairQuad_injective e⟩

end PairAddress

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem heq_of_paste {a a' b b' : C} (e : a = a') (f : b = b')
    {p : a ⟶ b} {q : a' ⟶ b'} (h : p ≫ eqToHom f = eqToHom e ≫ q) : HEq p q := by
  subst a'
  subst b'
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp, heq_eq_eq] using h

set_option backward.isDefEq.respectTransparency false in
theorem linCollect_map_heq {I : Type w} {K : Type z} (F : Lin 𝒮 Zₐ)
    (V : K → C) (f : I → K) (xs : List I) :
    HEq (F.collect (V ∘ f) xs) (F.collect V (xs.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Lin.collect]
    let D := fun i => F.obj (V i)
    let a := V (f x)
    have u := (std_fold_map V f xs).symm
    have v := (std_fold_map D f xs).symm
    refine structural_seq_heq (K:=coeff (C:=C)) (congrArg (fun c => (𝒮).obj (F.obj a) c) v)
      (congrArg (fun c => (𝒮).obj (F.obj a) (F.obj c)) u)
      (congrArg (fun c => F.obj ((𝒮).obj a c)) u) ?_ ?_
    · exact structural_map_heq (S:=𝒮) rfl rfl v (congrArg F.obj u) HEq.rfl ih
    · have k (b c : C) (h : b = c) : HEq (F.cons a b) (F.cons a c) := by subst c; rfl
      exact k _ _ u


set_option backward.isDefEq.respectTransparency false in
theorem gatherE_over_nested_heq {I K : Type*} (F : Lin 𝒮 Zₐ)
    (V : X → C) (tag : I → K → X) (rows : I → List K) (xs : List I) :
    HEq (GridExpr.gatherE F V
      (GridExpr.over (fun i => GridExpr.over (fun k => .leaf (tag i k)) (rows i)) xs))
      (act 𝒮 Zₐ (fun i => Lin.collect F (V ∘ tag i) (rows i)) xs ≫
        Lin.collect F (fun i => fold 𝒮 Zₐ (V ∘ tag i) (rows i)) xs) := by
  let P := fun i => GridExpr.over (fun k => .leaf (tag i k)) (rows i)
  let G := fun x => F.obj (V x)
  let p := fun i => GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G (fun k => .leaf (tag i k)) (rows i)
  let q := fun i => GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V (fun k => .leaf (tag i k)) (rows i)
  let a := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) G P xs).trans
    (congrArg (fun L => fold 𝒮 Zₐ L xs) (funext p))
  let b := (GridExpr.eval_over (S:=𝒮) (Z:=Zₐ) V P xs).trans
    (congrArg (fun L => fold 𝒮 Zₐ L xs) (funext q))
  apply heq_of_paste a (congrArg F.obj b)
  have h :
      eqToHom a.symm ≫ GridExpr.gatherE F V (GridExpr.over P xs) ≫ eqToHom (congrArg F.obj b) = _ :=
    gatherE_over_nested_collect F V tag rows xs
  have k := congrArg (fun m => eqToHom a ≫ m) h
  rw [← Category.assoc (eqToHom a), eqToHom_trans, eqToHom_refl, Category.id_comp] at k
  exact k


set_option backward.isDefEq.respectTransparency false in
theorem linCollect_rows_map_heq {I J K : Type u} (F : Lin 𝒮 Zₐ)
    (V : I → K → C) (f : I → J → K) (rows : I → List J) (xs : List I) :
    HEq
      (act 𝒮 Zₐ (fun i => F.collect (V i ∘ f i) (rows i)) xs ≫
        F.collect (fun i => fold 𝒮 Zₐ (V i ∘ f i) (rows i)) xs)
      (act 𝒮 Zₐ (fun i => F.collect (V i) ((rows i).map (f i))) xs ≫
        F.collect (fun i => fold 𝒮 Zₐ (V i) ((rows i).map (f i))) xs) := by
  let A := fun i => fold 𝒮 Zₐ (V i ∘ f i) (rows i)
  let B := fun i => fold 𝒮 Zₐ (V i) ((rows i).map (f i))
  let a : A = B := funext fun i => (std_fold_map (V i) (f i) (rows i)).symm
  let d := fun i => (std_fold_map (fun k => F.obj (V i k)) (f i) (rows i)).symm
  let k := fun i => congrArg F.obj (congrFun a i)
  have h := act_heq (funext d) (funext k)
    (fun i => linCollect_map_heq F (V i) (f i) (rows i)) xs
  have j : HEq (F.collect A xs) (F.collect B xs) := by
    have H {A B : I → C} (e : A = B) : HEq (F.collect A xs) (F.collect B xs) := by
      subst B
      rfl
    exact H a
  exact structural_seq_heq (K:=coeff (C:=C))
    (congrArg (fun U => fold 𝒮 Zₐ U xs) (funext d))
    (congrArg (fun U => fold 𝒮 Zₐ U xs) (funext k))
    (congrArg (fun U => F.obj (fold 𝒮 Zₐ U xs)) a) h j


section DecodeGather
variable {T : Bi (coeff (C:=C))} {I J : Type u}

theorem dependentExpr_eval_indexed (V : I → J → C) {K : Type u}
    (f : I → K → J) (xs : List I) (us : I → List K) :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun p : I × K => V p.1 (f p.1 p.2)) (dependentExpr xs us) =
      fold 𝒮 Zₐ (fun i => fold 𝒮 Zₐ (V i) ((us i).map (f i))) xs := by
  unfold dependentExpr
  rw [GridExpr.eval_over]
  apply congrArg (fun A => fold 𝒮 Zₐ A xs)
  funext i
  exact (GridExpr.eval_over _ _ _).trans (std_fold_map (V i) (f i) (us i)).symm

set_option backward.isDefEq.respectTransparency false in
theorem gatherE_dependent_mapped {K : Type u} (F : Lin 𝒮 Zₐ)
    (V : I → J → C) (f : I → K → J) (xs : List I) (us : I → List K) :
    HEq (GridExpr.gatherE F (fun p : I × K => V p.1 (f p.1 p.2)) (dependentExpr xs us))
      (act 𝒮 Zₐ (fun i => F.collect (V i) ((us i).map (f i))) xs ≫
        F.collect (fun i => fold 𝒮 Zₐ (V i) ((us i).map (f i))) xs) :=
  (gatherE_over_nested_heq F (fun p : I × K => V p.1 (f p.1 p.2)) Prod.mk us xs).trans
    (linCollect_rows_map_heq F V f us xs)

set_option backward.isDefEq.respectTransparency false in
theorem leftTreeGather_decode (L : LeftGather 𝒮 T Zₐ) (a : C)
    [(leftFactor T a).LaxBraided] (_h : SameLeftGather T a L)
    (P : I → C) (B : I → J → C) (ys : List I) (vs : I → List J) :
    HEq (GridExpr.gatherE (linearFunctor (leftFactor T a)) (dependentLabels (T:=T) P B) (dependentExpr ys vs))
      (act 𝒮 Zₐ (fun y => (Lin.left L a).collect (T.obj (P y)) ((vs y).map (B y))) ys ≫
        (Lin.left L a).collect (fun y => fold 𝒮 Zₐ (T.obj (P y)) ((vs y).map (B y))) ys) := by
  have e := gatherE_dependent_mapped (linearFunctor (leftFactor T a)) (fun y => T.obj (P y)) B ys vs
  have c : (fun y => Lin.collect (linearFunctor (leftFactor T a)) (T.obj (P y)) ((vs y).map (B y))) =
      (fun y => (Lin.left L a).collect (T.obj (P y)) ((vs y).map (B y))) :=
    funext fun y => leftFactor_sameCollect T a L _h _ _
  have d := leftFactor_sameCollect T a L _h (fun y => fold 𝒮 Zₐ (T.obj (P y)) ((vs y).map (B y))) ys
  rw [c, d] at e
  exact e

set_option backward.isDefEq.respectTransparency false in
theorem rightTreeGather_decode (R : Gather 𝒮 T Zₐ) (b : C)
    [(rightFactor (T:=T) b).LaxBraided] (_h : SameRightGather R b)
    (V : I → C) (A : I → J → C) (xs : List I) (us : I → List J) :
    HEq (GridExpr.gatherE (linearFunctor (rightFactor (T:=T) b)) (dependentLabels (T:=T) V A) (dependentExpr xs us))
      (act 𝒮 Zₐ (fun x => DependentFibre.gather R (T.obj (V x)) b ((us x).map (A x))) xs ≫
        DependentFibre.gather R (fun x => fold 𝒮 Zₐ (T.obj (V x)) ((us x).map (A x))) b xs) := by
  have e := gatherE_dependent_mapped (linearFunctor (rightFactor (T:=T) b)) (fun x => T.obj (V x)) A xs us
  have c : (fun x => Lin.collect (linearFunctor (rightFactor (T:=T) b)) (T.obj (V x)) ((us x).map (A x))) =
      (fun x => DependentFibre.gather R (T.obj (V x)) b ((us x).map (A x))) :=
    funext fun x => rightFactor_sameCollect R _h _ _
  have d := rightFactor_sameCollect R _h (fun x => fold 𝒮 Zₐ (T.obj (V x)) ((us x).map (A x))) xs
  rw [c, d] at e
  exact e

end DecodeGather

section Occurrence
set_option backward.isDefEq.respectTransparency false in
/-- The multiplicative schedule on the paired tree is the original
occurrence-first schedule, with the original lists of coefficients
recovered from their addressed child occurrences. -/
theorem treeGather_occurrenceFirst {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X U Y W : Type u} (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [∀ p : X × U, (leftFactor T (dependentLabels (T:=T) V A p)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
        (dependentExpr ys vs))).LaxBraided]
    (_hl : ∀ p : X × U, SameLeftGather T (dependentLabels (T:=T) V A p) L)
    (_hr : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
      (dependentExpr ys vs))) :
    let e := dependentExpr xs us
    let f := dependentExpr ys vs
    let A₀ := dependentLabels (T:=T) V A
    let B₀ := dependentLabels (T:=T) P B
    let b := GridExpr.eval (S:=𝒮) (Z:=Zₐ) B₀ f
    let right := fun p => GridExpr.gatherE (linearFunctor (leftFactor T (A₀ p))) B₀ f
    let left := GridExpr.gatherE (linearFunctor (rightFactor (T:=T) b)) A₀ e
    HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e ≫ left)
      (occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (P y))
        xs ys (indexInput A us).terms (indexInput B vs).terms) := by
  intro e f A₀ B₀ b right left
  let ta := (indexInput A us).terms
  let tb := (indexInput B vs).terms
  let f₀ := fun y => fold 𝒮 Zₐ (T.obj (P y)) (tb y)
  let e₀ := fun x => fold 𝒮 Zₐ (T.obj (V x)) (ta x)
  let b' := fold 𝒮 Zₐ f₀ ys
  let a' := fold 𝒮 Zₐ e₀ xs
  let evb : b = b' := dependentExpr_eval_indexed (fun y => T.obj (P y)) B ys vs
  let eva : GridExpr.eval (S:=𝒮) (Z:=Zₐ) A₀ e = a' :=
    dependentExpr_eval_indexed (fun x => T.obj (V x)) A xs us
  let row := fun (x : X) (a : C) => raggedCell (S:=𝒮) (Z:=Zₐ) (T:=T) (T.obj (V x)) tb (fun y => T.obj (P y)) a
  let k := fun (x : X) (a : C) =>
    act 𝒮 Zₐ (fun y => (Lin.left L (T.obj (V x) a)).collect (T.obj (P y)) (tb y)) ys ≫
      (Lin.left L (T.obj (V x) a)).collect f₀ ys
  let K := fun (x : X) => act 𝒮 Zₐ (k x) (ta x)
  let H := fun (x : X) => DependentFibre.gather R (T.obj (V x)) b' (ta x)
  have hRight : HEq (GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e) (act 𝒮 Zₐ K xs) := by
    unfold e dependentExpr K
    apply actE_over_decode right _
    · intro x
      rw [GridExpr.eval_over]
      apply (congrArg (fun M => fold 𝒮 Zₐ M (us x)) ?_).trans
        (std_fold_map (fun a => fold 𝒮 Zₐ (row x a) ys) (A x) (us x)).symm
      funext u
      exact dependentExpr_eval_indexed
        (fun y q => T.obj (T.obj (V x) (A x u)) (T.obj (P y) q)) B ys vs
    · intro x
      rw [GridExpr.eval_over]
      apply (congrArg (fun M => fold 𝒮 Zₐ M (us x)) ?_).trans
        (std_fold_map (fun a => T.obj (T.obj (V x) a) b') (A x) (us x)).symm
      exact funext fun u => congrArg (T.obj (T.obj (V x) (A x u))) evb
    · intro x
      refine HEq.trans ?_ (std_act_map_heq (A x) (k x) (us x))
      apply actE_over_decode right _ _ _ _ _ (us x)
      · intro u
        exact dependentExpr_eval_indexed
          (fun y q => T.obj (T.obj (V x) (A x u)) (T.obj (P y) q)) B ys vs
      · intro u
        exact congrArg (T.obj (T.obj (V x) (A x u))) evb
      · intro u
        exact leftTreeGather_decode L (A₀ (x,u)) (_hl (x,u)) P B ys vs
  have hLeft : HEq left
      (act 𝒮 Zₐ H xs ≫ DependentFibre.gather R e₀ b' xs) := by
    have q := rightTreeGather_decode R b _hr V A xs us
    have z {b₁ b₂ : C} (p : b₁ = b₂) :
      HEq
        (act 𝒮 Zₐ (fun x => DependentFibre.gather R (T.obj (V x)) b₁ (ta x)) xs ≫
          DependentFibre.gather R e₀ b₁ xs)
        (act 𝒮 Zₐ (fun x => DependentFibre.gather R (T.obj (V x)) b₂ (ta x)) xs ≫
          DependentFibre.gather R e₀ b₂ xs) := by cases p; rfl
    exact q.trans (z evb)
  have hx : (GridExpr.eval (S:=𝒮) (Z:=Zₐ)
      (fun p => GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun q => T.obj (A₀ p) (B₀ q)) f) e) =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun a => fold 𝒮 Zₐ (row x a) ys) (ta x)) xs := by
    apply dependentExpr_eval_indexed (fun x a => GridExpr.eval (S:=𝒮) (Z:=Zₐ)
      (fun q => T.obj (T.obj (V x) a) (B₀ q)) f) A xs us |>.trans
    apply congrArg (fun M => fold 𝒮 Zₐ M xs)
    funext x
    apply congrArg (fun M => fold 𝒮 Zₐ M (ta x))
    funext a
    exact dependentExpr_eval_indexed (fun y q => T.obj (T.obj (V x) a) (T.obj (P y) q)) B ys vs
  have hy : GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun p => T.obj (A₀ p) b) e =
      fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun a => T.obj (T.obj (V x) a) b') (ta x)) xs := by
    refine (dependentExpr_eval_indexed (fun x a => T.obj (T.obj (V x) a) b) A xs us).trans ?_
    exact congrArg (fun z => fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun a => T.obj (T.obj (V x) a) z) (ta x)) xs) evb
  have hz := congrArg₂ T.obj eva evb
  have q := structural_seq_heq (K:=coeff (C:=C)) hx hy hz hRight hLeft
  refine q.trans (heq_of_eq ?_)
  change (act 𝒮 Zₐ K xs ≫ act 𝒮 Zₐ H xs ≫ _) =
    act 𝒮 Zₐ (fun x => raggedRowGather R L (T.obj (V x)) (ta x) ys tb (fun y => T.obj (P y))) xs ≫ _
  have hc := act_seq (S:=𝒮) (Z:=Zₐ) K H xs
  change act 𝒮 Zₐ K xs ≫ act 𝒮 Zₐ H xs = act 𝒮 Zₐ (fun x => K x ≫ H x) xs at hc
  rw [reassoc_of% hc]
  congr 1
  apply congrArg (fun p => act 𝒮 Zₐ p xs)
  funext x
  let r := fun a => act 𝒮 Zₐ (fun y => (Lin.left L (T.obj (V x) a)).collect (T.obj (P y)) (tb y)) ys
  let s := fun a => (Lin.left L (T.obj (V x) a)).collect f₀ ys
  have hc' := act_seq (S:=𝒮) (Z:=Zₐ) r s (ta x)
  change act 𝒮 Zₐ r (ta x) ≫ act 𝒮 Zₐ s (ta x) = act 𝒮 Zₐ (fun a => r a ≫ s a) (ta x) at hc'
  change act 𝒮 Zₐ (fun a => r a ≫ s a) (ta x) ≫ H x =
    act 𝒮 Zₐ r (ta x) ≫ (act 𝒮 Zₐ s (ta x) ≫ H x)
  rw [← hc', Category.assoc]

end Occurrence

section PairGather
set_option backward.isDefEq.respectTransparency false in
theorem occurrencePairGather {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X U Y W : Type u} (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [∀ p : X × U, (leftFactor T (dependentLabels (T:=T) V A p)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
        (dependentExpr ys vs))).LaxBraided]
    (_hl : ∀ p : X × U, SameLeftGather T (dependentLabels (T:=T) V A p) L)
    (_hr : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
      (dependentExpr ys vs))) :
    let e := dependentExpr xs us
    let f := dependentExpr ys vs
    let A₀ := dependentLabels (T:=T) V A
    let B₀ := dependentLabels (T:=T) P B
    let Q := separateLeafLabels (T:=T) V P A B
    let G := fun p : (X × U) × (Y × W) => T.obj (A₀ p.1) (B₀ p.2)
    let src := fourOccurrenceExpr xs ys us vs
    let z := (std_fold_map Q pairQuad (e.leaves.product f.leaves)).symm
    let pin : fold 𝒮 Zₐ G (e.leaves.product f.leaves) = fold 𝒮 Zₐ Q src.leaves :=
      z.trans (congrArg (fold 𝒮 Zₐ Q) (congrArg (List.map pairQuad) (graftGrid_product_leaves e f).symm |>.trans
        ((retagGrid_leaves pairQuad (graftGrid (fun p => retagGrid (Prod.mk p) f) e)).symm.trans
          (congrArg GridExpr.leaves (nativeOccurrenceExpr_retag_product xs ys us vs)))))
    eqToHom pin ≫ compressGrid Q src ≫ eqToHom (raw_src_eq (T:=T) xs ys us vs V P A B) ≫
      occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (P y))
        xs ys (indexInput A us).terms (indexInput B vs).terms =
    rectWordChart G e.leaves f.leaves ≫ rowGather R L A₀ B₀ e.leaves f.leaves ≫
      T.map (compressGrid A₀ e ≫ eqToHom (dependentExpr_eval V A xs us))
        (compressGrid B₀ f ≫ eqToHom (dependentExpr_eval P B ys vs)) := by
  intro e f A₀ B₀ Q G src z pin
  let H := fun (p : X × U) => retagGrid (Prod.mk p) f
  let g := graftGrid H e
  let s := nativeOccurrenceExpr_retag_product xs ys us vs
  let right := fun p => GridExpr.gatherE (linearFunctor (leftFactor T (A₀ p))) B₀ f
  let b := GridExpr.eval (S:=𝒮) (Z:=Zₐ) B₀ f
  let left := GridExpr.gatherE (linearFunctor (rightFactor (T:=T) b)) A₀ e
  let k := GridExpr.actE (S:=𝒮) (Z:=Zₐ) right e ≫ left
  let c₀ := dependentExpr_eval (T:=T) V A xs us
  let d₀ := dependentExpr_eval (T:=T) P B ys vs
  let cd := congrArg₂ T.obj c₀ d₀
  let evalQ := GridExpr.eval (S:=𝒮) (Z:=Zₐ) Q
  let F := fold 𝒮 Zₐ Q
  let p₀ := (congrArg (fold 𝒮 Zₐ G) (graftGrid_product_leaves e f).symm)
  let rr := retagGrid_eval Q pairQuad g
  let r := congrArg F (retagGrid_leaves pairQuad g)
  let t := std_fold_map Q pairQuad g.leaves
  let h := (graftGrid_eval G H e).trans
      (congrArg (fun J => GridExpr.eval (S:=𝒮) (Z:=Zₐ) J e)
        (funext fun x => retagGrid_eval G (Prod.mk x) f))
  let hc := congrArg evalQ s
  let hs := raw_src_eq (T:=T) xs ys us vs V P A B
  let occ := occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (P y))
        xs ys (indexInput A us).terms (indexInput B vs).terms
  have hh : k ≫ eqToHom cd = eqToHom (h.symm.trans (rr.symm.trans (hc.trans hs))) ≫ occ := by
    apply heq_paste _ cd
    exact treeGather_occurrenceFirst R L V P A B xs ys us vs _hl _hr
  have hr : compressGrid Q (retagGrid pairQuad g) ≫ eqToHom rr = eqToHom (r.trans t) ≫ compressGrid G g :=
    compressGrid_retag Q pairQuad g
  have hflat := graftedProduct_flatGather R L A₀ B₀ e f _hl _hr
  have hT {a a' b b' : C} (p : a = a') (q : b = b') :
      T.map (eqToHom p) (eqToHom q) = eqToHom (congrArg₂ T.obj p q) := by
    cases p
    cases q
    exact T.map_id _ _
  have hlift :
      T.map (compressGrid A₀ e) (compressGrid B₀ f) ≫ eqToHom cd =
      T.map (compressGrid A₀ e ≫ eqToHom c₀) (compressGrid B₀ f ≫ eqToHom d₀) := by
    rw [← hT c₀ d₀]
    exact (T.map_seq _ _ _ _).symm
  have hcomp : compressGrid Q src =
      eqToHom (congrArg (fun x => F x.leaves) s.symm) ≫
        compressGrid Q (retagGrid pairQuad g) ≫ eqToHom hc := by
    have H {g₁ g₂ : GridExpr (X × U × Y × W)} (s : g₁ = g₂) :
        compressGrid Q g₂ =
          eqToHom (congrArg (fun x => F x.leaves) s.symm) ≫
            compressGrid Q g₁ ≫ eqToHom (congrArg evalQ s) := by
      cases s
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact H s
  have hf :
      eqToHom p₀ ≫ compressGrid G g ≫ eqToHom h ≫ k =
        rectWordChart G e.leaves f.leaves ≫ rowGather R L A₀ B₀ e.leaves f.leaves ≫
          T.map (compressGrid A₀ e) (compressGrid B₀ f) := by
    have H := hflat
    dsimp only at H
    exact H
  symm
  rw [← hlift]
  rw [← reassoc_of% hf, hh]
  rw [← Category.assoc (eqToHom h), eqToHom_trans]
  have hp : h.trans (h.symm.trans (rr.symm.trans (hc.trans hs))) = rr.symm.trans (hc.trans hs) :=
    Subsingleton.elim _ _
  rw [hp, ← eqToHom_trans rr.symm (hc.trans hs)]
  have hr' : compressGrid G g ≫ eqToHom rr.symm =
      eqToHom (r.trans t).symm ≫ compressGrid Q (retagGrid pairQuad g) := by
    have H := congrArg (fun a => eqToHom (r.trans t).symm ≫ a ≫ eqToHom rr.symm) hr
    simp only [Category.assoc] at H
    simp only [eqToHom_trans_assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id, Category.id_comp] at H
    exact H.symm
  simp only [Category.assoc]
  rw [reassoc_of% hr', ← eqToHom_trans hc hs, hcomp]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom p₀), eqToHom_trans,
    ← Category.assoc (eqToHom pin), eqToHom_trans]

end PairGather

section FlatSeparate
variable {T : Bi (coeff (C:=C))} {X U Y W : Type u}

theorem occurrencePairPin (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    fold 𝒮 Zₐ (fun p : (X × U) × (Y × W) =>
      T.obj (dependentLabels (T:=T) V A p.1) (dependentLabels (T:=T) P B p.2))
      ((dependentWord xs us).product (dependentWord ys vs)) =
    fold 𝒮 Zₐ (separateLeafLabels (T:=T) V P A B) (fourOccurrenceExpr xs ys us vs).leaves :=
  (std_fold_map (separateLeafLabels (T:=T) V P A B) pairQuad
    ((dependentWord xs us).product (dependentWord ys vs))).symm.trans
    (congrArg (fold 𝒮 Zₐ (separateLeafLabels (T:=T) V P A B))
      (nativeOccurrenceExpr_word_product xs ys us vs))

set_option backward.isDefEq.respectTransparency false in
theorem occurrencePairGather_word
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [∀ p : X × U, (leftFactor T (dependentLabels (T:=T) V A p)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
        (dependentExpr ys vs))).LaxBraided]
    (_hl : ∀ p : X × U, SameLeftGather T (dependentLabels (T:=T) V A p) L)
    (_hr : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
      (dependentExpr ys vs))) :
    let e := dependentExpr xs us
    let f := dependentExpr ys vs
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    let A₀ := dependentLabels (T:=T) V A
    let B₀ := dependentLabels (T:=T) P B
    let Q := separateLeafLabels (T:=T) V P A B
    let G := fun p : (X × U) × (Y × W) => T.obj (A₀ p.1) (B₀ p.2)
    let src := fourOccurrenceExpr xs ys us vs
    let c := eqToHom (congrArg (fold 𝒮 Zₐ A₀) (dependentExpr_leaves xs us).symm) ≫
      compressGrid A₀ e ≫ eqToHom (dependentExpr_eval V A xs us)
    let d := eqToHom (congrArg (fold 𝒮 Zₐ B₀) (dependentExpr_leaves ys vs).symm) ≫
      compressGrid B₀ f ≫ eqToHom (dependentExpr_eval P B ys vs)
    eqToHom (occurrencePairPin (T:=T) V P A B xs ys us vs) ≫ compressGrid Q src ≫
      eqToHom (raw_src_eq (T:=T) xs ys us vs V P A B) ≫
      occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (P y))
        xs ys (indexInput A us).terms (indexInput B vs).terms =
    rectWordChart G xw yw ≫ rowGather R L A₀ B₀ xw yw ≫ T.map c d := by
  intro e f xw yw A₀ B₀ Q G src c d
  let ea := dependentExpr_leaves xs us
  let eb := dependentExpr_leaves ys vs
  have H {xw' : List (X × U)} {yw' : List (Y × W)} (ha : xw' = e.leaves) (hb : yw' = f.leaves)
      (q : fold 𝒮 Zₐ G (e.leaves.product f.leaves) ⟶ _) :
      q = rectWordChart G e.leaves f.leaves ≫ rowGather R L A₀ B₀ e.leaves f.leaves ≫
        T.map (compressGrid A₀ e ≫ eqToHom (dependentExpr_eval V A xs us))
          (compressGrid B₀ f ≫ eqToHom (dependentExpr_eval P B ys vs)) →
      eqToHom (congrArg (fold 𝒮 Zₐ G) (congrArg₂ List.product ha hb)) ≫ q =
        rectWordChart G xw' yw' ≫ rowGather R L A₀ B₀ xw' yw' ≫
          T.map (eqToHom (congrArg (fold 𝒮 Zₐ A₀) ha) ≫
            compressGrid A₀ e ≫ eqToHom (dependentExpr_eval V A xs us))
            (eqToHom (congrArg (fold 𝒮 Zₐ B₀) hb) ≫
            compressGrid B₀ f ≫ eqToHom (dependentExpr_eval P B ys vs)) := by
    subst xw'
    subst yw'
    simp only [eqToHom_refl, Category.id_comp, imp_self]
  have p := occurrencePairGather R L V P A B xs ys us vs _hl _hr
  dsimp only at p
  have q := H ea.symm eb.symm _ p
  simp only [← Category.assoc, eqToHom_trans] at q
  simp only [Category.assoc] at q
  exact q


set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem bi_map_comp {T : Bi (coeff (C:=C))} {a a' a'' b b' b'' : C}
    (p : a ⟶ a') (q : a' ⟶ a'') (r : b ⟶ b') (s : b' ⟶ b'') :
    T.map p r ≫ T.map q s = T.map (p ≫ q) (r ≫ s) :=
  (T.map_seq p q r s).symm

section Routes
set_option backward.isDefEq.respectTransparency false in
theorem separateWordAug_pair
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [∀ p : X × U, (leftFactor T (dependentLabels (T:=T) V A p)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
        (dependentExpr ys vs))).LaxBraided]
    (_hl : ∀ p : X × U, SameLeftGather T (dependentLabels (T:=T) V A p) L)
    (_hr : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
      (dependentExpr ys vs)))
    {I : C} (J : UnitCompat R I)
    (δ : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A us) x ⟶ I)
    (δ' : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B vs) y ⟶ I)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (ε' : fold 𝒮 Zₐ P ys ⟶ I) :
    let A₀ := dependentLabels (T:=T) V A
    let B₀ := dependentLabels (T:=T) P B
    let G := fun z : (X × U) × (Y × W) => T.obj (A₀ z.1) (B₀ z.2)
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    eqToHom (occurrencePairPin (T:=T) V P A B xs ys us vs) ≫
      separateWordAug xs ys us vs V P A B R L J δ δ' ε ε' =
    rectWordChart G xw yw ≫ rowGather R L A₀ B₀ xw yw ≫
      T.map (dependentWordAugCell R L J xs us V A δ ε)
        (dependentWordAugCell R L J ys vs P B δ' ε') ≫ J.ρ I := by
  intro A₀ B₀ G xw yw
  unfold separateWordAug separateGlobalAug dependentWordAugCell
  have h := occurrencePairGather_word R L V P A B xs ys us vs _hl _hr
  dsimp only at h
  rw [reassoc_of% h, reassoc_of% bi_map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem separateWordCell_pair
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (V : X → C) (P : Y → C) (A : X → U → C) (B : Y → W → C)
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
    [∀ p : X × U, (leftFactor T (dependentLabels (T:=T) V A p)).LaxBraided]
    [(rightFactor (T:=T) (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
        (dependentExpr ys vs))).LaxBraided]
    (_hl : ∀ p : X × U, SameLeftGather T (dependentLabels (T:=T) V A p) L)
    (_hr : SameRightGather R (GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) P B)
      (dependentExpr ys vs)))
    {a b c d : C}
    (β : ∀ x, inner (S:=𝒮) (Z:=Zₐ) (indexInput A us) x ⟶ b)
    (θ : ∀ y, inner (S:=𝒮) (Z:=Zₐ) (indexInput B vs) y ⟶ d)
    (α : fold 𝒮 Zₐ V xs ⟶ a) (γ : fold 𝒮 Zₐ P ys ⟶ c) :
    let A₀ := dependentLabels (T:=T) V A
    let B₀ := dependentLabels (T:=T) P B
    let G := fun z : (X × U) × (Y × W) => T.obj (A₀ z.1) (B₀ z.2)
    let xw := dependentWord xs us
    let yw := dependentWord ys vs
    let one := eqToHom (congrArg (fold 𝒮 Zₐ A₀) (dependentExpr_leaves xs us).symm) ≫
      compressGrid A₀ (dependentExpr xs us) ≫ eqToHom (dependentExpr_eval V A xs us) ≫
        dep R V (indexInput A us) L xs β α
    let two := eqToHom (congrArg (fold 𝒮 Zₐ B₀) (dependentExpr_leaves ys vs).symm) ≫
      compressGrid B₀ (dependentExpr ys vs) ≫ eqToHom (dependentExpr_eval P B ys vs) ≫
        dep R P (indexInput B vs) L ys θ γ
    eqToHom (occurrencePairPin (T:=T) V P A B xs ys us vs) ≫
      separateWordCell xs ys us vs V P A B R L β θ α γ =
    rectWordChart G xw yw ≫ rowGather R L A₀ B₀ xw yw ≫ T.map one two := by
  intro A₀ B₀ G xw yw one two
  unfold separateWordCell separateNestedCell
  have h := occurrencePairGather_word R L V P A B xs ys us vs _hl _hr
  dsimp only at h
  rw [reassoc_of% h, bi_map_comp]
  simp only [Category.assoc, one, two]
  rfl

end Routes
end FlatSeparate
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
