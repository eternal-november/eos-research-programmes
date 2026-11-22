module
public import ContextualComposition.NativeIndependentPartition

@[expose] public section
/-! The actual native independent product arrow and its literal selected
whole-fibre cells in a stable pair-tagged rectangular word. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

private theorem product_cons_pin {X Y : Type w} (x : X) (xs : List X) (ys : List Y) :
    (x :: xs).product ys = ys.map (fun y => (x,y)) ++ xs.product ys := rfl

private theorem pair_mem_product {X Y : Type w} {x : X} {y : Y} {xs : List X} {ys : List Y} :
    (x,y) ∈ xs.product ys ↔ x ∈ xs ∧ y ∈ ys := by
  change (x,y) ∈ xs.flatMap (fun x => ys.map (fun y => (x,y))) ↔ _
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,rfl,rfl⟩
    exact ⟨ha,hb⟩
  · rintro ⟨hx,hy⟩
    exact ⟨x,hx,y,hy,rfl,rfl⟩

theorem nodup_product_word {X Y : Type w} {xs : List X} {ys : List Y}
    (hx : xs.Nodup) (hy : ys.Nodup) : (xs.product ys).Nodup := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
    rw [product_cons_pin, List.nodup_append]
    apply And.intro
    · exact hy.map (fun y => (x,y)) (fun a b hn h => hn (congrArg Prod.snd h))
    · have hh := List.nodup_cons.mp hx
      refine ⟨ih hh.2, ?_⟩
      intro a ha b hb h
      rcases List.mem_map.mp ha with ⟨y,_,rfl⟩
      cases h
      exact hh.1 (pair_mem_product.mp hb).1

theorem product_word_fibre {X Y X' Y' : Type w} [DecidableEq X'] [DecidableEq Y']
    (xs : List X) (ys : List Y) (f : X → X') (g : Y → Y') (t : X' × Y') :
    wordFibre (xs.product ys) (Prod.map f g) t =
      (wordFibre xs f t.1).product (wordFibre ys g t.2) := by
  rcases t with ⟨a,b⟩
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    let e := (fun z => decide (Prod.map f g z = (a,b))) ∘ (fun y => (x,y))
    have z : List.filter (fun _ => false) ys = [] :=
      List.filter_eq_nil_iff.mpr (fun _ _ => by decide)
    by_cases hx : f x = a
    · have e' : e = (fun y => decide (g y = b)) := by
        funext y
        change decide ((f x, g y) = (a,b)) = _
        simp [hx]
      simp only [wordFibre, List.filter_cons, hx, decide_true, ite_true, product_cons_pin,
        List.filter_append, List.filter_map]
      change List.map (fun y => (x,y)) (ys.filter e) ++ wordFibre (xs.product ys) (Prod.map f g) (a,b) =
        List.map (fun y => (x,y)) (wordFibre ys g b) ++ (wordFibre xs f a).product (wordFibre ys g b)
      rw [e', ih]
      rfl
    · have e' : e = (fun _ => false) := by
        funext y
        change decide ((f x, g y) = (a,b)) = false
        simp [hx]
      simp only [wordFibre, product_cons_pin, List.filter_cons, hx, decide_false,
        Bool.false_eq_true, ite_false, List.filter_append, List.filter_map]
      change List.map (fun y => (x,y)) (ys.filter e) ++ wordFibre (xs.product ys) (Prod.map f g) (a,b) = _
      rw [e', z, List.map_nil, List.nil_append]
      exact ih

/-- Two noninjective axes retain all four addressed occurrences; the
same rectangle chart permits an independently empty target-axis fibre. -/
theorem product_fibre_addressed_empty :
    let f : Fin 2 → Fin 2 := fun _ => 0
    let xs := List.finRange 2
    wordFibre (xs.product xs) (Prod.map f f) (0,0) = [(0,0),(0,1),(1,0),(1,1)] ∧
      wordFibre (xs.product xs) (Prod.map f f) (0,1) = [] := by
  decide

def rectWordChart {X Y : Type w} (A : X × Y → C) (xs : List X) (ys : List Y) :
    fold 𝒮 Zₐ A (xs.product ys) ⟶ fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys) xs :=
  rowsChart A (fun x => ys.map (fun y => (x,y))) xs ≫
    act 𝒮 Zₐ (fun x => eqToHom (std_fold_map A (fun y => (x,y)) ys)) xs

set_option backward.isDefEq.respectTransparency false in
/-- Exact nesting of the literal flat pair-row partition. The target rows
remain present when one of their component fibres is empty. -/
theorem rowsChart_rectWord {S X Y : Type w} (A : S → C) (L : X × Y → List S)
    (xs : List X) (ys : List Y) :
    let R := fun x => ys.map (fun y => (x,y))
    let e : (xs.product ys).flatMap L = xs.flatMap (fun x => ys.flatMap (fun y => L (x,y))) :=
      (List.flatMap_assoc (l:=xs) (f:=R) (g:=L)).trans
        (congrArg (fun k => xs.flatMap k) (funext fun x => List.flatMap_map (fun y => (x,y)) L ys))
    rowsChart A L (xs.product ys) ≫ rectWordChart (fun p => fold 𝒮 Zₐ A (L p)) xs ys =
      eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫
      rowsChart A (fun x => ys.flatMap (fun y => L (x,y))) xs ≫
      act 𝒮 Zₐ (fun x => rowsChart A (fun y => L (x,y)) ys) xs := by
  intro R e
  let F := fold 𝒮 Zₐ A
  let B := fun p => F (L p)
  let L₁ := fun x => (R x).flatMap L
  let L₂ := fun x => ys.flatMap (fun y => L (x,y))
  let E (x : X) : L₁ x = L₂ x := List.flatMap_map (fun y => (x,y)) L ys
  let q₀ := rowsChart A L (xs.product ys)
  let q₁ := rowsChart B R xs
  let q₂ := fun x => eqToHom (std_fold_map B (fun y => (x,y)) ys)
  let p₁ := rowsChart A L₁ xs
  let p₂ := fun x => rowsChart A L (R x)
  let p₃ := fun x => rowsChart A (fun y => L (x,y)) ys
  let t := fun x => eqToHom (congrArg F (E x))
  let h₀ := List.flatMap_assoc (l:=xs) (f:=R) (g:=L)
  let a := eqToHom (congrArg F h₀)
  let b := eqToHom (congrArg F (congrArg (fun k => xs.flatMap k) (funext E)))
  have h₁ : q₀ ≫ q₁ = a ≫ p₁ ≫ act 𝒮 Zₐ p₂ xs := by
    let ai := eqToHom (congrArg F h₀.symm)
    let _ : IsIso ai := inferInstanceAs (IsIso (eqToHom (congrArg F h₀.symm)))
    apply (cancel_epi ai).mp
    have hh : ai ≫ q₀ ≫ q₁ = p₁ ≫ act 𝒮 Zₐ p₂ xs := rowsChart_iterated A L R xs
    have h : ai ≫ a = 𝟙 _ := by
      change eqToHom _ ≫ eqToHom _ = _
      rw [eqToHom_trans]
      rfl
    simp only [reassoc_of% h]
    exact hh
  have h₂ (x : X) : p₂ x ≫ q₂ x = t x ≫ p₃ x := rowsChart_relabel_index A L (fun y => (x,y)) ys
  have h₃ : act 𝒮 Zₐ p₂ xs ≫ act 𝒮 Zₐ q₂ xs = act 𝒮 Zₐ t xs ≫ act 𝒮 Zₐ p₃ xs :=
    (act_seq 𝒮 Zₐ p₂ q₂ xs).trans ((congrArg (fun k => act 𝒮 Zₐ k xs) (funext h₂)).trans (act_seq 𝒮 Zₐ t p₃ xs).symm)
  have ht : act 𝒮 Zₐ t xs = eqToHom (congrArg (fun A => fold 𝒮 Zₐ A xs)
      (funext fun x => congrArg F (E x))) := std_act_eqToHom _ _
  have h₄ : p₁ ≫ act 𝒮 Zₐ t xs = b ≫ rowsChart A L₂ xs := by
    let Q : X → List S := L₂
    have H : L₁ = Q := funext E
    -- The formula is just substitution of equal raw rows, not a quotient.
    have K (P Q : X → List S) (H : P = Q) :
        rowsChart A P xs ≫ eqToHom (congrArg (fun E => fold 𝒮 Zₐ E xs)
          (funext fun x => congrArg F (congrFun H x))) =
        eqToHom (congrArg F (congrArg (fun E => xs.flatMap E) H)) ≫ rowsChart A Q xs := by
      cases H
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rw [ht]
    exact K L₁ Q H
  change q₀ ≫ (q₁ ≫ act 𝒮 Zₐ q₂ xs) = _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  let c₀ := congrArg F h₀
  let c₁ := congrArg F (congrArg (fun k => xs.flatMap k) (funext E))
  change a ≫ p₁ ≫ (act 𝒮 Zₐ p₂ xs ≫ act 𝒮 Zₐ q₂ xs) =
    eqToHom (c₀.trans c₁) ≫ rowsChart A L₂ xs ≫ act 𝒮 Zₐ p₃ xs
  rw [h₃, ← Category.assoc p₁, h₄]
  simp only [Category.assoc]
  rw [← Category.assoc a]
  congr 1
  exact eqToHom_trans _ _

set_option backward.isDefEq.respectTransparency false in
theorem rectWordChart_natural {X Y : Type w} {A B : X × Y → C}
    (p : ∀ t, A t ⟶ B t) (xs : List X) (ys : List Y) :
    act 𝒮 Zₐ p (xs.product ys) ≫ rectWordChart B xs ys =
      rectWordChart A xs ys ≫ act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => p (x,y)) ys) xs := by
  let f := fun (x : X) (y : Y) => (x,y)
  let L := fun x => ys.map (f x)
  let a := fun x => eqToHom (std_fold_map A (f x) ys)
  let b := fun x => eqToHom (std_fold_map B (f x) ys)
  let r := fun x => act 𝒮 Zₐ p (L x)
  let q := fun x => act 𝒮 Zₐ (fun y => p (f x y)) ys
  have h (x : X) : r x ≫ b x = a x ≫ q x := (std_act_map A (f x) p ys).symm
  have h' : act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ b xs = act 𝒮 Zₐ a xs ≫ act 𝒮 Zₐ q xs :=
    (act_seq 𝒮 Zₐ r b xs).trans ((congrArg (fun k => act 𝒮 Zₐ k xs) (funext h)).trans (act_seq 𝒮 Zₐ a q xs).symm)
  have e : act 𝒮 Zₐ p (xs.product ys) ≫ rowsChart B L xs =
      rowsChart A L xs ≫ act 𝒮 Zₐ r xs := rowsChart_natural L p xs
  change act 𝒮 Zₐ p (xs.product ys) ≫ (rowsChart B L xs ≫ act 𝒮 Zₐ b xs) =
    (rowsChart A L xs ≫ act 𝒮 Zₐ a xs) ≫ act 𝒮 Zₐ q xs
  rw [← Category.assoc, e]
  simp only [Category.assoc, h']

def rectWordAxisOrder {X Y : Type w} {xs xs' : List X} {ys ys' : List Y}
    (p : AddressOrder X xs xs') (q : AddressOrder Y ys ys') :
    AddressOrder (X × Y) (xs.product ys) (xs'.product ys') :=
  (rowOrders (fun x => q.relabel (fun y => (x,y))) xs).seq
    (liftRows (fun x => ys'.map (fun y => (x,y))) p)

set_option backward.isDefEq.respectTransparency false in
theorem rectWordChart_axis_order {X Y : Type w} (A : X × Y → C)
    {xs xs' : List X} {ys ys' : List Y}
    (p : AddressOrder X xs xs') (q : AddressOrder Y ys ys') :
    AddressOrder.mapSum additiveStructure A (rectWordAxisOrder p q) ≫ rectWordChart A xs' ys' =
    rectWordChart A xs ys ≫
      (act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (fun y => A (x,y)) q) xs ≫
        AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys') p) := by
  let f := fun (x : X) (y : Y) => (x,y)
  let L := fun x => ys.map (f x)
  let L' := fun x => ys'.map (f x)
  let a := fun x => eqToHom (std_fold_map A (f x) ys)
  let a' := fun x => eqToHom (std_fold_map A (f x) ys')
  let r := fun x => AddressOrder.mapSum additiveStructure A (q.relabel (f x))
  let q₀ := fun x => AddressOrder.mapSum additiveStructure (fun y => A (x,y)) q
  let p₀ := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun y => A (x,y)) ys') p
  let p₁ := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ A (L' x)) p
  let R := AddressOrder.mapSum additiveStructure A (rowOrders (fun x => q.relabel (f x)) xs)
  let P := AddressOrder.mapSum additiveStructure A (liftRows L' p)
  have h (x : X) : r x ≫ a' x = a x ≫ q₀ x := (relabel_mapSum A (f x) q).symm
  have h' : act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ a' xs = act 𝒮 Zₐ a xs ≫ act 𝒮 Zₐ q₀ xs :=
    (act_seq 𝒮 Zₐ r a' xs).trans ((congrArg (fun k => act 𝒮 Zₐ k xs) (funext h)).trans (act_seq 𝒮 Zₐ a q₀ xs).symm)
  have e : R ≫ rowsChart A L' xs = rowsChart A L xs ≫ act 𝒮 Zₐ r xs :=
    rowsChart_rowOrders A (fun x => q.relabel (f x)) xs
  have e' : P ≫ rowsChart A L' xs' = rowsChart A L' xs ≫ p₁ := rowsChart_liftRows A L' p
  have m : p₁ ≫ act 𝒮 Zₐ a' xs' = act 𝒮 Zₐ a' xs ≫ p₀ :=
    (AddressOrder.natural additiveNaturality a' p).symm
  change (R ≫ P) ≫ (rowsChart A L' xs' ≫ act 𝒮 Zₐ a' xs') =
    (rowsChart A L xs ≫ act 𝒮 Zₐ a xs) ≫ (act 𝒮 Zₐ q₀ xs ≫ p₀)
  simp only [Category.assoc]
  rw [reassoc_of% e', m, reassoc_of% e, reassoc_of% h']

variable (T : Bi (coeff (C:=C)))
abbrev independentWord (A B : Family C) := (List.finRange A.n).product (List.finRange B.n)
abbrev independentLabels (A B : Family C) (p : Fin A.n × Fin B.n) := T.obj (A.val p.1) (B.val p.2)
abbrev independentFamily (A B : Family C) := wordFamily (independentLabels T A B) (independentWord A B)

variable {A B A' B' : Family C} (p : Hom ℙ A A') (q : Hom ℙ B B')

theorem independent_get_fibre (p : Hom ℙ A A') (q : Hom ℙ B B') (t : Fin A'.n × Fin B'.n) :
    wordFibre (independentWord A B) (Prod.map p.addr q.addr) t =
      (fibreList p.addr t.1).product (fibreList q.addr t.2) := by
  rw [product_word_fibre]
  simp only [wordFibre, fibreList, beq_eq_decide]

theorem independent_word_support (p : Hom ℙ A A') (q : Hom ℙ B B') :
    ∀ t ∈ independentWord A B, (Prod.map p.addr q.addr) t ∈ independentWord A' B' := by
  intro t _
  rcases t with ⟨i,j⟩
  exact pair_mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def independentWordCell (T : Bi (coeff (C:=C))) (p : Hom ℙ A A') (q : Hom ℙ B B') (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (t : Fin A'.n × Fin B'.n) :
    fold 𝒮 Zₐ (independentLabels T A B) (wordFibre (independentWord A B) (Prod.map p.addr q.addr) t) ⟶
      independentLabels T A' B' t :=
  eqToHom (congrArg (fold 𝒮 Zₐ (independentLabels T A B)) (independent_get_fibre p q t)) ≫
    rectWordChart (independentLabels T A B) (fibreList p.addr t.1) (fibreList q.addr t.2) ≫
    independentCell R L A.val B.val (fibreList p.addr t.1) (fibreList q.addr t.2) (p.cell t.1) (q.cell t.2)

noncomputable def independentNativeWordMap (T : Bi (coeff (C:=C))) (p : Hom ℙ A A') (q : Hom ℙ B B') (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) :
    Hom ℙ (independentFamily T A B) (independentFamily T A' B') :=
  wordNativeMap (Prod.map p.addr q.addr) (independent_word_support p q)
    (nodup_product_word (List.nodup_finRange _) (List.nodup_finRange _))
    (independentLabels T A B) (independentLabels T A' B')
    (fun i => independentWordCell T p q R L (independentWord A' B')[i])

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
