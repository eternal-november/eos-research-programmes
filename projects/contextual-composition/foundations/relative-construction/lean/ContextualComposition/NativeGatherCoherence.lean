module
public import ContextualComposition.BinaryAugmentedSquareBridge

@[expose] public section
/-! Flattening and partitioning the actual recursively gathered lists.
The structural hypotheses are the standard local axioms of an additive
lax braided functor, not a native partition or augmentation equation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
open Functor.LaxMonoidal
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

abbrev linearFunctor (F : C ⥤ C) [F.LaxMonoidal] : Lin 𝒮 Zₐ where
  obj := F.obj
  map := F.map
  id := F.map_id
  seq := F.map_comp
  nil := ε F
  cons := μ F

section Gather
variable (F : C ⥤ C) [F.LaxMonoidal]
variable {X : Type w} (A : X → C)
local notation "c" => Lin.collect (linearFunctor F) A
local notation "xFold" => fold 𝒮 Zₐ A
local notation "G" => fun x => F.obj (A x)
local notation "j" => join additiveStructure A
local notation "k" => join additiveStructure G

set_option backward.isDefEq.respectTransparency false in
theorem collect_singleton (x : X) :
    c [x] ≫ F.map (ρ_ (A x)).hom = (ρ_ (F.obj (A x))).hom := by
  change ((𝟙 (F.obj (A x)) ⊗ₘ ε F) ≫ μ F (A x) Zₐ) ≫ F.map (ρ_ (A x)).hom =
    (ρ_ (F.obj (A x))).hom
  rw [id_tensorHom, Category.assoc]
  exact (right_unitality F _).symm

set_option backward.isDefEq.respectTransparency false in
theorem collect_join (xs ys : List X) :
    k xs ys ≫ (c xs ⊗ₘ c ys) ≫ μ F (xFold xs) (xFold ys) =
      c (xs ++ ys) ≫ F.map (j xs ys) := by
  induction xs with
  | nil =>
    let p : fold 𝒮 Zₐ G ys ⟶ F.obj (xFold ys) := c ys
    change (λ_ _).inv ≫ (ε F ⊗ₘ p) ≫ μ F Zₐ (xFold ys) = p ≫ F.map (λ_ (xFold ys)).inv
    rw [ε_tensorHom_comp_μ, leftUnitor_naturality_assoc,
      Iso.inv_hom_id_assoc]
  | cons a xs ih =>
    let s := xFold xs
    let t := xFold ys
    let u := A a
    let v := F.obj u
    let s' := fold 𝒮 Zₐ G xs
    let t' := fold 𝒮 Zₐ G ys
    let c₁ : s' ⟶ F.obj s := c xs
    let c₂ : t' ⟶ F.obj t := c ys
    let c₃ := c (xs ++ ys)
    let J : xFold (xs ++ ys) ⟶ s ⊗ t := j xs ys
    let K : fold 𝒮 Zₐ G (xs ++ ys) ⟶ s' ⊗ t' := k xs ys
    have e₁ : k (a::xs) ys = (v ◁ K) ≫ (α_ v s' t').inv := std_join_cons G a xs ys
    have e₂ : j (a::xs) ys = (u ◁ J) ≫ (α_ u s t).inv := std_join_cons A a xs ys
    rw [e₁, e₂]
    change ((v ◁ K) ≫ (α_ v s' t').inv) ≫ (((𝟙 v ⊗ₘ c₁) ≫ μ F u s) ⊗ₘ c₂) ≫ μ F (u ⊗ s) t =
      ((𝟙 v ⊗ₘ c₃) ≫ μ F u (xFold (xs ++ ys))) ≫ F.map ((u ◁ J) ≫ (α_ u s t).inv)
    rw [id_tensorHom, id_tensorHom]
    have e : (((v ◁ c₁) ≫ μ F u s) ⊗ₘ c₂) =
        ((v ◁ c₁) ⊗ₘ c₂) ≫ μ F u s ▷ F.obj t := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
    rw [e, F.map_comp]
    let R := μ F u s ▷ F.obj t
    have α := associator_inv_naturality (𝟙 v) c₁ c₂
    rw [id_tensorHom, id_tensorHom] at α
    simp only [Category.assoc]
    rw [← reassoc_of% α, ← Functor.LaxMonoidal.associativity_inv F u s t]
    have H : K ≫ (c₁ ⊗ₘ c₂) ≫ μ F s t = c₃ ≫ F.map J := ih
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, H,
      whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc]


set_option backward.isDefEq.respectTransparency false in
theorem collect_pair (a b : X) (xs : List X) :
    c (a::b::xs) =
      (F.obj (A a) ◁ F.obj (A b) ◁ c xs) ≫
      (α_ (F.obj (A a)) (F.obj (A b)) (F.obj (xFold xs))).inv ≫
      μ F (A a) (A b) ▷ F.obj (xFold xs) ≫
      μ F (A a ⊗ A b) (xFold xs) ≫ F.map (α_ (A a) (A b) (xFold xs)).hom := by
  let u := A a
  let v := A b
  let w := xFold xs
  let s := c xs
  change (𝟙 (F.obj u) ⊗ₘ ((𝟙 (F.obj v) ⊗ₘ s) ≫ μ F v w)) ≫ μ F u (v ⊗ w) = _
  rw [id_tensorHom, id_tensorHom, whiskerLeft_comp, Category.assoc, whiskerLeft_μ_comp_μ]

end Gather

section BraidedGather
variable (F : C ⥤ C) [F.LaxBraided]
variable {X : Type w} (A : X → C)
local notation "c" => Lin.collect (linearFunctor F) A
local notation "xFold" => fold 𝒮 Zₐ A
local notation "G" => fun x => F.obj (A x)
set_option backward.isDefEq.respectTransparency false in
theorem collect_swap (a b : X) (xs : List X) :
    crossHead (F.obj (A a)) (F.obj (A b)) (fold 𝒮 Zₐ G xs) ≫ c (b::a::xs) =
      c (a::b::xs) ≫ F.map (crossHead (A a) (A b) (xFold xs)) := by
  rw [collect_pair, collect_pair]
  let u := A a
  let v := A b
  let w := xFold xs
  let U := F.obj u
  let V := F.obj v
  let W := F.obj w
  let s := c xs
  have nat := crossHead_nat U V s
  rw [← Category.assoc (crossHead _ _ _), nat, Category.assoc]
  change (U ◁ V ◁ s) ≫ crossHead U V W ≫ (α_ V U W).inv ≫
      μ F v u ▷ W ≫ μ F (v ⊗ u) w ≫ F.map (α_ v u w).hom =
    ((U ◁ V ◁ s) ≫ (α_ U V W).inv ≫ μ F u v ▷ W ≫ μ F (u ⊗ v) w ≫
      F.map (α_ u v w).hom) ≫ F.map (crossHead u v w)
  unfold crossHead
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← F.map_comp, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, ← Functor.LaxBraided.braided,
    comp_whiskerRight_assoc, μ_natural_left_assoc, F.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem order_swap_standard (a b : X) (xs : List X) :
    AddressOrder.mapSum additiveStructure A (.swap a b xs) = crossHead (A a) (A b) (xFold xs) := by
  change (α_ _ _ _).inv ≫ ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom = _
  rw [tensorHom_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem collect_order {xs ys : List X} (p : AddressOrder X xs ys) :
    AddressOrder.mapSum additiveStructure G p ≫ c ys =
      c xs ≫ F.map (AddressOrder.mapSum additiveStructure A p) := by
  induction p with
  | ident =>
    change 𝟙 _ ≫ _ = _ ≫ F.map (𝟙 _)
    rw [F.map_id, Category.id_comp, Category.comp_id]
  | swap a b xs =>
    rw [order_swap_standard G, order_swap_standard A]
    exact collect_swap F A a b xs
  | @keep a xs ys p ih =>
    let P := AddressOrder.mapSum additiveStructure A p
    let Q := AddressOrder.mapSum additiveStructure G p
    let U := F.obj (A a)
    change (𝟙 U ⊗ₘ Q) ≫ ((𝟙 U ⊗ₘ c ys) ≫ μ F (A a) (xFold ys)) =
      ((𝟙 U ⊗ₘ c xs) ≫ μ F (A a) (xFold xs)) ≫ F.map (𝟙 (A a) ⊗ₘ P)
    rw [id_tensorHom, id_tensorHom, id_tensorHom, id_tensorHom,
      ← whiskerLeft_comp_assoc, ih, whiskerLeft_comp, Category.assoc, μ_natural_right]
    simp only [Category.assoc]
    rfl
  | seq p q hp hq =>
    change (AddressOrder.mapSum additiveStructure G p ≫ AddressOrder.mapSum additiveStructure G q) ≫
      c _ = c _ ≫ F.map (AddressOrder.mapSum additiveStructure A p ≫ AddressOrder.mapSum additiveStructure A q)
    rw [Category.assoc, hq, ← Category.assoc, hp, Category.assoc, F.map_comp]

end BraidedGather

section Rows
variable (F : C ⥤ C) [F.LaxMonoidal]
variable {X : Type w} {Y : Type z} (A : X → C) (L : Y → List X)

set_option backward.isDefEq.respectTransparency false in
theorem collect_rows (ys : List Y) :
    rowsChart (fun x => F.obj (A x)) L ys ≫
      act 𝒮 Zₐ (fun y => Lin.collect (linearFunctor F) A (L y)) ys ≫
      Lin.collect (linearFunctor F) (fun y => fold 𝒮 Zₐ A (L y)) ys =
    Lin.collect (linearFunctor F) A (ys.flatMap L) ≫ F.map (rowsChart A L ys) := by
  induction ys with
  | nil =>
    change 𝟙 Zₐ ≫ 𝟙 Zₐ ≫ ε F = ε F ≫ F.map (𝟙 Zₐ)
    rw [F.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  | cons y ys ih =>
    let A₀ := L y
    let A₁ := ys.flatMap L
    let J := fun x => F.obj (A x)
    let P := fun y => fold 𝒮 Zₐ A (L y)
    let Q := fold 𝒮 Zₐ P ys
    let C₀ := fold 𝒮 Zₐ A A₀
    let C₁ := fold 𝒮 Zₐ A A₁
    let u : fold 𝒮 Zₐ J A₀ ⟶ F.obj C₀ := Lin.collect (linearFunctor F) A A₀
    let v : fold 𝒮 Zₐ J A₁ ⟶ F.obj C₁ := Lin.collect (linearFunctor F) A A₁
    let s := Lin.collect (linearFunctor F) P ys
    let X₀ := rowsChart J L ys
    let X₁ := act 𝒮 Zₐ (fun y => Lin.collect (linearFunctor F) A (L y)) ys
    let Y₀ := rowsChart A L ys
    let K : fold 𝒮 Zₐ J (A₀ ++ A₁) ⟶ fold 𝒮 Zₐ J A₀ ⊗ fold 𝒮 Zₐ J A₁ :=
      join additiveStructure J A₀ A₁
    let M : fold 𝒮 Zₐ A (A₀ ++ A₁) ⟶ C₀ ⊗ C₁ := join additiveStructure A A₀ A₁
    let c := Lin.collect (linearFunctor F) A (A₀ ++ A₁)
    change (K ≫ (𝟙 _ ⊗ₘ X₀)) ≫ (u ⊗ₘ X₁) ≫
      (𝟙 (F.obj C₀) ⊗ₘ s) ≫ μ F C₀ Q =
      c ≫ F.map (M ≫ (𝟙 C₀ ⊗ₘ Y₀))
    have I : X₀ ≫ X₁ ≫ s = v ≫ F.map Y₀ := ih
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp]
    rw [I]
    have e : u ⊗ₘ (v ≫ F.map Y₀) = (u ⊗ₘ v) ≫ (F.obj C₀ ◁ F.map Y₀) := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
    rw [e, Category.assoc, μ_natural_right, F.map_comp]
    have h : K ≫ (u ⊗ₘ v) ≫ μ F C₀ C₁ = c ≫ F.map M := collect_join F A A₀ A₁
    simp only [id_tensorHom]
    rw [reassoc_of% h]

end Rows

section Native
variable (F : C ⥤ C) [F.LaxBraided]
local notation "K" => linearFunctor F
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem collect_partition {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (A : Fin n → C) (j : Fin l) :
    standardPushSplit f g (fun i => F.obj (A i)) j ≫
      standardPushMap g (fun y => Lin.collect K A (fibreList f y)) j ≫
      Lin.collect K (standardPushObj f A) (fibreList g j) =
    Lin.collect K A (fibreList (g ∘ f) j) ≫ F.map (standardPushSplit f g A j) := by
  let P := splitOrder f g j
  let ys := fibreList g j
  let L := fibreList f
  let G := fun x => F.obj (A x)
  let r := AddressOrder.mapSum additiveStructure G P
  let s := AddressOrder.mapSum additiveStructure A P
  let k := rowsChart G L ys
  let l := rowsChart A L ys
  let c := Lin.collect K A (fibreList (g ∘ f) j)
  have v := collect_rows F A L ys
  have w := collect_order F A P
  change (r ≫ k) ≫ (act 𝒮 Zₐ (fun y => Lin.collect K A (L y)) ys ≫
    Lin.collect K (fun y => fold 𝒮 Zₐ A (L y)) ys) = c ≫ F.map (s ≫ l)
  change k ≫ act 𝒮 Zₐ (fun y => Lin.collect K A (L y)) ys ≫
    Lin.collect K (fun y => fold 𝒮 Zₐ A (L y)) ys = Lin.collect K A (ys.flatMap L) ≫ F.map l at v
  change r ≫ Lin.collect K A (ys.flatMap L) = c ≫ F.map s at w
  rw [Category.assoc, v, ← Category.assoc, w, Category.assoc, F.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem collect_map_naturality {X : Type w} {A B : X → C} (p : ∀ x, A x ⟶ B x) (xs : List X) :
    act 𝒮 Zₐ (fun x => F.map (p x)) xs ≫ Lin.collect K B xs =
      Lin.collect K A xs ≫ F.map (act 𝒮 Zₐ p xs) := by
  induction xs with
  | nil =>
    change 𝟙 Zₐ ≫ ε F = ε F ≫ F.map (𝟙 Zₐ)
    rw [F.map_id, Category.id_comp, Category.comp_id]
  | cons x xs ih =>
    let u := p x
    let a := A x
    let b := B x
    let c := fold 𝒮 Zₐ A xs
    let d := fold 𝒮 Zₐ B xs
    let p₀ := act 𝒮 Zₐ p xs
    let p₁ := act 𝒮 Zₐ (fun x => F.map (p x)) xs
    let A₀ := Lin.collect K A xs
    let B₀ := Lin.collect K B xs
    change (F.map u ⊗ₘ p₁) ≫ (𝟙 (F.obj b) ⊗ₘ B₀) ≫ μ F b d =
      ((𝟙 (F.obj a) ⊗ₘ A₀) ≫ μ F a c) ≫ F.map (u ⊗ₘ p₀)
    rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]
    have E : p₁ ≫ B₀ = A₀ ≫ F.map p₀ := ih
    rw [E, ← Category.id_comp (F.map u), ← tensorHom_comp_tensorHom_assoc, μ_natural, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
theorem collect_list_congr {X : Type w} (A : X → C) {xs ys : List X} (e : xs = ys) :
    Lin.collect K A xs ≫ F.map (eqToHom (congrArg (fold 𝒮 Zₐ A) e)) =
      eqToHom (congrArg (fold 𝒮 Zₐ (fun x => F.obj (A x))) e) ≫ Lin.collect K A ys := by
  subst ys
  simp only [eqToHom_refl, F.map_id, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem collect_standard_single {n : Nat} (A : Fin n → C) (j : Fin n) :
    Lin.collect K A (fibreList id j) ≫ F.map (standardPushSingle A j) =
      standardPushSingle (fun x => F.obj (A x)) j := by
  let e := fibreList_id j
  let G := fun x => F.obj (A x)
  change Lin.collect K A (fibreList id j) ≫
      F.map (eqToHom (congrArg (fold 𝒮 Zₐ A) e) ≫ (ρ_ (A j)).hom) =
      eqToHom (congrArg (fold 𝒮 Zₐ G) e) ≫ (ρ_ (F.obj (A j))).hom
  rw [F.map_comp, ← Category.assoc, collect_list_congr F A e, Category.assoc, collect_singleton]

def linearFamily (A : Family C) : Family C := ⟨A.n, fun i => F.obj (A.val i)⟩

noncomputable def linearNativeMap {A B : Family C} (p : Hom ℙ A B) :
    Hom ℙ (linearFamily F A) (linearFamily F B) :=
  ⟨p.addr, fun j => Lin.collect K A.val (fibreList p.addr j) ≫ F.map (p.cell j)⟩

theorem linearNativeMap_ident (A : Family C) :
    linearNativeMap F (Hom.ident A) = Hom.ident (linearFamily F A) := by
  apply congrArg (Hom.mk id)
  funext j
  exact collect_standard_single F A.val j

set_option backward.isDefEq.respectTransparency false in
theorem linearNativeMap_comp {A B D : Family C} (p : Hom ℙ A B) (q : Hom ℙ B D) :
    linearNativeMap F (p.comp q) = (linearNativeMap F p).comp (linearNativeMap F q) := by
  apply congrArg (Hom.mk (S:=ℙ) (A:=linearFamily F A) (B:=linearFamily F D) (q.addr ∘ p.addr))
  funext j
  let f := p.addr
  let g := q.addr
  let a := A.val
  let b := B.val
  let r := fun i => Lin.collect K a (fibreList f i)
  let u := standardPushMap g p.cell j
  let v := Lin.collect K b (fibreList g j)
  let s := standardPushSplit f g a j
  let t := standardPushSplit f g (fun i => F.obj (a i)) j
  let z := Lin.collect K (standardPushObj f a) (fibreList g j)
  let w := Lin.collect K a (fibreList (g ∘ f) j)
  change w ≫ F.map (s ≫ u ≫ q.cell j) =
      t ≫ standardPushMap g (fun i => r i ≫ F.map (p.cell i)) j ≫ v ≫ F.map (q.cell j)
  have n : standardPushMap g (fun i => F.map (p.cell i)) j ≫ v = z ≫ F.map u :=
    collect_map_naturality F p.cell (fibreList g j)
  have h : t ≫ standardPushMap g r j ≫ z = w ≫ F.map s :=
    collect_partition F f g a j
  rw [standardPushMap_comp, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% n, reassoc_of% h]

noncomputable def linearAug {I : C} (A : Aug ℙ I) : Aug ℙ (F.obj I) :=
  ⟨linearFamily F A.base, linearNativeMap F A.ε⟩

noncomputable def linearAugMap {I : C} {A B : Aug ℙ I} (p : AugHom ℙ A B) :
    AugHom ℙ (linearAug F A) (linearAug F B) where
  native := linearNativeMap F p.native
  preserves := by
    change (linearNativeMap F p.native).comp (linearNativeMap F B.ε) = linearNativeMap F A.ε
    rw [← linearNativeMap_comp, p.preserves]

end Native

section Trees
variable (F : C ⥤ C) [F.LaxMonoidal] {I : Type u} (A : I → C)
local notation "K" => linearFunctor F

set_option backward.isDefEq.respectTransparency false in
/-- Flattening the actual nested gather, with syntactic zero subtrees kept
until they are consumed by the functor's prescribed unit. -/
theorem collect_compressGrid (t : GridExpr I) :
    compressGrid (fun i => F.obj (A i)) t ≫ GridExpr.gatherE K A t =
      Lin.collect K A t.leaves ≫ F.map (compressGrid A t) := by
  induction t with
  | zero =>
    change 𝟙 Zₐ ≫ ε F = ε F ≫ F.map (𝟙 Zₐ)
    rw [F.map_id, Category.id_comp, Category.comp_id]
  | leaf a =>
    change (ρ_ (F.obj (A a))).hom ≫ 𝟙 _ =
      Lin.collect K A [a] ≫ F.map (ρ_ (A a)).hom
    rw [Category.comp_id, collect_singleton]
  | bin l r hl hr =>
    let G := fun x => F.obj (A x)
    let E := GridExpr.eval (S:=𝒮) (Z:=Zₐ) A
    let fl := fold 𝒮 Zₐ A l.leaves
    let fr := fold 𝒮 Zₐ A r.leaves
    let J : fold 𝒮 Zₐ A (l.leaves ++ r.leaves) ⟶ fl ⊗ fr := join additiveStructure A l.leaves r.leaves
    let J' : fold 𝒮 Zₐ G (l.leaves ++ r.leaves) ⟶
        fold 𝒮 Zₐ G l.leaves ⊗ fold 𝒮 Zₐ G r.leaves := join additiveStructure G l.leaves r.leaves
    let L := compressGrid A l
    let R := compressGrid A r
    let cₗ := Lin.collect K A l.leaves
    let cᵣ := Lin.collect K A r.leaves
    let c := Lin.collect K A (l.leaves ++ r.leaves)
    change (J' ≫ (compressGrid G l ⊗ₘ compressGrid G r)) ≫
        ((GridExpr.gatherE K A l ⊗ₘ GridExpr.gatherE K A r) ≫ μ F (E l) (E r)) =
      c ≫ F.map (J ≫ (L ⊗ₘ R))
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc]
    rw [hl, hr]
    change J' ≫ ((cₗ ≫ F.map L) ⊗ₘ (cᵣ ≫ F.map R)) ≫ μ F (E l) (E r) =
      c ≫ F.map (J ≫ (L ⊗ₘ R))
    rw [← tensorHom_comp_tensorHom, Category.assoc, μ_natural, F.map_comp]
    have h : J' ≫ (cₗ ⊗ₘ cᵣ) ≫ μ F fl fr = c ≫ F.map J := collect_join F A l.leaves r.leaves
    rw [reassoc_of% h]
end Trees

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
