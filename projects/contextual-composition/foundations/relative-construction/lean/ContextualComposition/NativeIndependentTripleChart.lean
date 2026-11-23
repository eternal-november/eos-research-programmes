module
public import ContextualComposition.NativeIndependentTripleGather
@[expose] public section

/-! Charts for the independent triple rectangle, separating occurrence
readings from distributivity. Both operations admit empty axes. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem collect_rectWordChart (F : C ⥤ C) [F.LaxBraided] {X Y : Type u}
    (A : X × Y → C) (xs : List X) (ys : List Y) :
    let K := linearFunctor F
    rectWordChart (F.obj ∘ A) xs ys ≫
      act 𝒮 Zₐ (fun x => K.collect (A ∘ Prod.mk x) ys) xs ≫
      K.collect (fun x => fold 𝒮 Zₐ (A ∘ Prod.mk x) ys) xs =
    K.collect A (xs.product ys) ≫ F.map (rectWordChart A xs ys) :=
  collect_taggedRaggedRows F A Prod.mk (fun _ => ys) xs

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
local notation "a" => fold 𝒮 Zₐ A xs
local notation "b" => fold 𝒮 Zₐ B ys
local notation "d" => fold 𝒮 Zₐ D ws
local notation "lft" => Lin.left L
local notation "rgt" => Lin.right R

set_option backward.isDefEq.respectTransparency false in
include NL in
theorem rightTriple_collected (c : C)
    [lax : (leftFactor T c).LaxBraided] (hl : SameLeftGather T c L) :
    let G := crossLabel T B D
    let q := rectWordChart G ys ws ≫ rowGather R L B D ys ws
    (lft c).collect G (ys.product ws) ≫ T.map (𝟙 c) q =
      rectWordChart (fun z => T.obj c (G z)) ys ws ≫
        act 𝒮 Zₐ (fun y => ((lft (B y)).comp (lft c)).collect D ws) ys ≫
        ((rgt d).comp (lft c)).collect B ys := by
  intro G q
  let F := leftFactor T c
  let V := fun y => fold 𝒮 Zₐ (fun w => T.obj (B y) (D w)) ws
  let e := fun y => (lft (B y)).collect D ws
  let n := fun y => (lft c).collect (fun w => T.obj (B y) (D w)) ws
  let p := fun y => ((lft (B y)).comp (lft c)).collect D ws
  let t := (rgt d).collect B ys
  have h₀ : q = rectWordChart G ys ws ≫ act 𝒮 Zₐ e ys ≫ t := by
    have ht : DependentFibre.gather R B d ys = t := (collect_right_eq R B ys d).symm
    change rectWordChart G ys ws ≫ (act 𝒮 Zₐ e ys ≫ DependentFibre.gather R B d ys) = _
    rw [ht]
  have h₁ : (lft c).collect G (ys.product ws) ≫ F.map (rectWordChart G ys ws) =
      rectWordChart (F.obj ∘ G) ys ws ≫ act 𝒮 Zₐ n ys ≫ (lft c).collect V ys := by
    have j := collect_rectWordChart F G ys ws
    dsimp only at j
    simp only [F, leftFactor_sameCollect T c L hl] at j
    exact j.symm
  have h₂ : (lft c).collect V ys ≫ F.map (act 𝒮 Zₐ e ys) =
      act 𝒮 Zₐ (fun y => F.map (e y)) ys ≫ (lft c).collect (fun y => T.obj (B y) d) ys :=
    (Lin.collect_nat (lft c) (NL.inner c) e ys).symm
  have h₃ : (lft c).collect (fun y => T.obj (B y) d) ys ≫ F.map t =
      ((rgt d).comp (lft c)).collect B ys :=
    (Lin.collect_comp (rgt d) (lft c) (NL.inner c) B ys).symm
  have h₄ : act 𝒮 Zₐ n ys ≫ act 𝒮 Zₐ (fun y => F.map (e y)) ys = act 𝒮 Zₐ p ys := by
    have h (y : Y) : n y ≫ F.map (e y) = p y :=
      (Lin.collect_comp (lft (B y)) (lft c) (NL.inner c) D ws).symm
    exact (act_seq 𝒮 Zₐ n _ ys).trans (congrArg (fun f => act 𝒮 Zₐ f ys) (funext h))
  change (lft c).collect G (ys.product ws) ≫ F.map q = _
  rw [h₀, F.map_comp, F.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄, h₃]
  rfl


def tripleRightFlatGather :=
  let G := crossLabel T B D
  rectWordChart (crossLabel T A G) xs (ys.product ws) ≫
    rowGather R L A G xs (ys.product ws) ≫
    T.map (𝟙 a) (rectWordChart G ys ws ≫ rowGather R L B D ys ws)

set_option backward.isDefEq.respectTransparency false in
include NL in
theorem tripleRightFlatGather_chart
    [lF : ∀ t : C, (leftFactor T t).LaxBraided] (hl : ∀ t : C, SameLeftGather T t L) :
    let G := crossLabel T B D
    let H := crossLabel T A G
    tripleRightFlatGather R L A B D xs ys ws =
      rectWordChart H xs (ys.product ws) ≫
        act 𝒮 Zₐ (fun x => rectWordChart (H ∘ Prod.mk x) ys ws) xs ≫
        tripleIndependentRawRight R L A B D xs ys ws := by
  intro G H
  let q := rectWordChart G ys ws ≫ rowGather R L B D ys ws
  let p := fun x => (lft (A x)).collect G (ys.product ws)
  let v := fun x => (leftFactor T (A x)).map q
  let t := fun x => rectWordChart (H ∘ Prod.mk x) ys ws
  let r := fun x => act 𝒮 Zₐ (fun y => ((lft (B y)).comp (lft (A x))).collect D ws) ys
  let s := fun x => ((rgt d).comp (lft (A x))).collect B ys
  let u := DependentFibre.gather R A (T.obj b d) xs
  have h : DependentFibre.gather R A (fold 𝒮 Zₐ G (ys.product ws)) xs ≫ T.map (𝟙 a) q =
      act 𝒮 Zₐ v xs ≫ u := gather_nat R A q xs
  have h₀ (x : X) : p x ≫ v x = t x ≫ r x ≫ s x := rightTriple_collected R L NL B D ys ws (A x) (hl _)
  have h₁ : act 𝒮 Zₐ p xs ≫ act 𝒮 Zₐ v xs =
      act 𝒮 Zₐ t xs ≫ act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ s xs :=
    (act_seq 𝒮 Zₐ p v xs).trans ((congrArg (fun f => act 𝒮 Zₐ f xs) (funext h₀)).trans
      ((act_seq 𝒮 Zₐ t (fun x => r x ≫ s x) xs).symm.trans
        (congrArg (fun l => act 𝒮 Zₐ t xs ≫ l) (act_seq 𝒮 Zₐ r s xs).symm)))
  unfold tripleRightFlatGather rowGather tally
  change rectWordChart H xs (ys.product ws) ≫
    (act 𝒮 Zₐ p xs ≫ DependentFibre.gather R A (fold 𝒮 Zₐ G (ys.product ws)) xs) ≫ T.map (𝟙 a) q = _
  simp only [Category.assoc]
  rw [h, reassoc_of% h₁]
  unfold tripleIndependentRawRight
  rw [collect_right_eq]


set_option backward.isDefEq.respectTransparency false in
include NR in
theorem leftTriple_collected (c : C)
    [lax : (rightFactor (T:=T) c).LaxBraided] (hr : SameRightGather R c) :
    let G := crossLabel T A B
    let q := rectWordChart G xs ys ≫ rowGather R L A B xs ys
    (rgt c).collect G (xs.product ys) ≫ T.map q (𝟙 c) =
      rectWordChart (fun z => T.obj (G z) c) xs ys ≫
        act 𝒮 Zₐ (fun x => ((lft (A x)).comp (rgt c)).collect B ys) xs ≫
        ((rgt b).comp (rgt c)).collect A xs := by
  intro G q
  let F := rightFactor (T:=T) c
  let V := fun x => fold 𝒮 Zₐ (fun y => T.obj (A x) (B y)) ys
  let e := fun x => (lft (A x)).collect B ys
  let n := fun x => (rgt c).collect (fun y => T.obj (A x) (B y)) ys
  let p := fun x => ((lft (A x)).comp (rgt c)).collect B ys
  let t := (rgt b).collect A xs
  have h₀ : q = rectWordChart G xs ys ≫ act 𝒮 Zₐ e xs ≫ t := by
    have ht : DependentFibre.gather R A b xs = t := (collect_right_eq R A xs b).symm
    change rectWordChart G xs ys ≫ (act 𝒮 Zₐ e xs ≫ DependentFibre.gather R A b xs) = _
    rw [ht]
  have h₁ : (rgt c).collect G (xs.product ys) ≫ F.map (rectWordChart G xs ys) =
      rectWordChart (F.obj ∘ G) xs ys ≫ act 𝒮 Zₐ n xs ≫ (rgt c).collect V xs := by
    have j := collect_rectWordChart F G xs ys
    dsimp only at j
    simp only [F, rightFactor_sameCollect R hr, ← collect_right_eq] at j
    exact j.symm
  have h₂ : (rgt c).collect V xs ≫ F.map (act 𝒮 Zₐ e xs) =
      act 𝒮 Zₐ (fun x => F.map (e x)) xs ≫ (rgt c).collect (fun x => T.obj (A x) b) xs :=
    (Lin.collect_nat (rgt c) (rightNatural R NR c) e xs).symm
  have h₃ : (rgt c).collect (fun x => T.obj (A x) b) xs ≫ F.map t =
      ((rgt b).comp (rgt c)).collect A xs :=
    (Lin.collect_comp (rgt b) (rgt c) (rightNatural R NR c) A xs).symm
  have h₄ : act 𝒮 Zₐ n xs ≫ act 𝒮 Zₐ (fun x => F.map (e x)) xs = act 𝒮 Zₐ p xs := by
    have h (x : X) : n x ≫ F.map (e x) = p x :=
      (Lin.collect_comp (lft (A x)) (rgt c) (rightNatural R NR c) B ys).symm
    exact (act_seq 𝒮 Zₐ n _ xs).trans (congrArg (fun f => act 𝒮 Zₐ f xs) (funext h))
  change (rgt c).collect G (xs.product ys) ≫ F.map q = _
  rw [h₀, F.map_comp, F.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄, h₃]
  rfl

def tripleLeftFlatGather :=
  let G := crossLabel T A B
  rectWordChart (crossLabel T G D) (xs.product ys) ws ≫
    rowGather R L G D (xs.product ys) ws ≫
    T.map (rectWordChart G xs ys ≫ rowGather R L A B xs ys) (𝟙 d)

set_option backward.isDefEq.respectTransparency false in
include NR in
theorem tripleLeftFlatGather_chart
    [rF : ∀ t : C, (rightFactor (T:=T) t).LaxBraided] (hr : ∀ t : C, SameRightGather R t) :
    let H := crossLabel T (crossLabel T A B) D
    let f := fun (x : X) (z : Y × W) => ((x,z.1),z.2)
    tripleLeftFlatGather R L A B D xs ys ws =
      eqToHom (congrArg (fold 𝒮 Zₐ H) (tripleWord_flat xs (fun _ => ys) (fun _ _ => ws))) ≫
      taggedRaggedRows H f (fun _ => ys.product ws) xs ≫
        act 𝒮 Zₐ (fun x => rectWordChart (H ∘ f x) ys ws) xs ≫
        tripleIndependentRawLeft R L A B D xs ys ws := by
  intro H f
  let G := crossLabel T A B
  let B₀ := fun z : X × Y => T.obj (G z) d
  let q := rectWordChart G xs ys ≫ rowGather R L A B xs ys
  let p := fun z : X × Y => (lft (G z)).collect D ws
  let r := fun x => ((lft (A x)).comp (rgt d)).collect B ys
  let s := ((rgt b).comp (rgt d)).collect A xs
  have h : DependentFibre.gather R G d (xs.product ys) ≫ T.map q (𝟙 d) =
      rectWordChart B₀ xs ys ≫ act 𝒮 Zₐ r xs ≫ s := by
    rw [← collect_right_eq]
    exact leftTriple_collected R L NR A B xs ys d (hr _)
  have h₀ := nestedDependentRows H B₀ xs (fun _ => ys) (fun _ _ => ws) p
  change rectWordChart H (xs.product ys) ws ≫ act 𝒮 Zₐ p (xs.product ys) ≫ rectWordChart B₀ xs ys =
    eqToHom (congrArg (fold 𝒮 Zₐ H) (tripleWord_flat xs (fun _ => ys) (fun _ _ => ws))) ≫
      taggedRaggedRows H f (fun _ => ys.product ws) xs ≫
      act 𝒮 Zₐ (fun x => rectWordChart (H ∘ f x) ys ws ≫ act 𝒮 Zₐ (fun y => p (x,y)) ys) xs at h₀
  unfold tripleLeftFlatGather rowGather tally
  change rectWordChart H (xs.product ys) ws ≫
    (act 𝒮 Zₐ p (xs.product ys) ≫ DependentFibre.gather R G d (xs.product ys)) ≫ T.map q (𝟙 d) = _
  simp only [Category.assoc]
  rw [h, reassoc_of% h₀, ← act_seq]
  simp only [Category.assoc]
  rfl


def tripleFlatChart (H : X × Y × W → C) (xs : List X) (ys : List Y) (ws : List W) :=
  rectWordChart H xs (ys.product ws) ≫ act 𝒮 Zₐ (fun x => rectWordChart (H ∘ Prod.mk x) ys ws) xs

set_option backward.isDefEq.respectTransparency false in
theorem tripleFlatChart_natural {H K : X × Y × W → C}
    (p : ∀ t, H t ⟶ K t) (xs : List X) (ys : List Y) (ws : List W) :
    act 𝒮 Zₐ p (xs.product (ys.product ws)) ≫ tripleFlatChart K xs ys ws =
      tripleFlatChart H xs ys ws ≫ act 𝒮 Zₐ (fun x => act 𝒮 Zₐ
        (fun y => act 𝒮 Zₐ (fun w => p (x,y,w)) ws) ys) xs := by
  let u := fun x => act 𝒮 Zₐ (fun v => p (x,v)) (ys.product ws)
  let v := fun x => rectWordChart (K ∘ Prod.mk x) ys ws
  let l := fun x => rectWordChart (H ∘ Prod.mk x) ys ws
  let r := fun x => act 𝒮 Zₐ (fun y => act 𝒮 Zₐ (fun w => p (x,y,w)) ws) ys
  have h : act 𝒮 Zₐ p (xs.product (ys.product ws)) ≫ rectWordChart K xs (ys.product ws) =
      rectWordChart H xs (ys.product ws) ≫ act 𝒮 Zₐ u xs := rectWordChart_natural p xs _
  have k (x : X) : u x ≫ v x = l x ≫ r x := rectWordChart_natural (fun t => p (x,t)) ys ws
  have kk : act 𝒮 Zₐ u xs ≫ act 𝒮 Zₐ v xs = act 𝒮 Zₐ l xs ≫ act 𝒮 Zₐ r xs :=
    (act_seq 𝒮 Zₐ u v xs).trans
      ((congrArg (fun g => act 𝒮 Zₐ g xs) (funext k)).trans (act_seq 𝒮 Zₐ l r xs).symm)
  unfold tripleFlatChart
  rw [← Category.assoc, h, Category.assoc]
  change rectWordChart H xs (ys.product ws) ≫ (act 𝒮 Zₐ u xs ≫ act 𝒮 Zₐ v xs) = _
  rw [kk, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
include NR in
theorem tripleLeftFlatGather_read
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c) :
    let H := crossLabel T (crossLabel T A B) D
    let G := H ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
    HEq (tripleLeftFlatGather R L A B D xs ys ws)
      (tripleFlatChart G xs ys ws ≫ tripleIndependentRawLeft R L A B D xs ys ws) := by
  intro H G
  let f := fun (x : X) (z : Y × W) => ((x,z.1),z.2)
  let g := (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
  let h₀ := tripleWord_flat xs (fun _ => ys) (fun _ _ => ws)
  let F := fold 𝒮 Zₐ H
  let w := xs.product (ys.product ws)
  let p := fun x => rectWordChart (G ∘ Prod.mk x) ys ws
  let q := tripleIndependentRawLeft R L A B D xs ys ws
  have a₀ : tripleLeftFlatGather R L A B D xs ys ws =
      eqToHom (congrArg F h₀) ≫ taggedRaggedRows H f (fun _ => ys.product ws) xs ≫ act 𝒮 Zₐ p xs ≫ q :=
    tripleLeftFlatGather_chart R L NR A B D xs ys ws hr
  have hh : HEq (taggedRaggedRows H f (fun _ => ys.product ws) xs)
      (rectWordChart G xs (ys.product ws)) :=
    (taggedRaggedRows_tag_heq H g Prod.mk (fun _ => ys.product ws) xs).symm
  have hread : w.map g = xs.flatMap (fun x => (ys.product ws).map (f x)) := by
    change (xs.flatMap (fun x => (ys.product ws).map (Prod.mk x))).map g =
      xs.flatMap (fun x => (ys.product ws).map (f x))
    simp only [List.map_flatMap, List.map_map]
    rfl
  let e₀ := (congrArg F hread.symm).trans (std_fold_map H g w)
  have h₁ : HEq (taggedRaggedRows H f (fun _ => ys.product ws) xs ≫ (act 𝒮 Zₐ p xs ≫ q))
      (rectWordChart G xs (ys.product ws) ≫ (act 𝒮 Zₐ p xs ≫ q)) :=
    structural_seq_heq (K:=coeff (C:=C)) e₀ rfl rfl hh HEq.rfl
  rw [a₀]
  exact (hom_source_pin_heq (congrArg F h₀) _).trans
    (h₁.trans (heq_of_eq (Category.assoc _ _ _).symm))

set_option backward.isDefEq.respectTransparency false in
include NR NL in
/-- The two literal triple distributions, before any selected whole
cells, are compared on the ordered raw triple addresses. -/
theorem tripleFlatGather_assoc (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
    [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c) :
    HEq (tripleLeftFlatGather R L A B D xs ys ws ≫ P.assoc a b d)
      (act 𝒮 Zₐ (fun t : X × Y × W => P.assoc (A t.1) (B t.2.1) (D t.2.2)) (xs.product (ys.product ws)) ≫
        tripleRightFlatGather R L A B D xs ys ws) := by
  let H := crossLabel T (crossLabel T A B) D
  let G := H ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
  let K := crossLabel T A (crossLabel T B D)
  let p (t : X × Y × W) : G t ⟶ K t := P.assoc (A t.1) (B t.2.1) (D t.2.2)
  let w := xs.product (ys.product ws)
  let v := (xs.product ys).product ws
  let q := P.assoc a b d
  let G₀ : fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun z => G (x,y,z)) ws) ys) xs ⟶
      T.obj (T.obj a b) d := tripleIndependentRawLeft R L A B D xs ys ws
  let G₁ : fold 𝒮 Zₐ (fun x => fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (fun z => K (x,y,z)) ws) ys) xs ⟶
      T.obj a (T.obj b d) := tripleIndependentRawRight R L A B D xs ys ws
  let e := (std_fold_map G tripleRetag v).symm.trans
    (congrArg (fold 𝒮 Zₐ G) (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)))
  have hl' := tripleLeftFlatGather_read R L NR A B D xs ys ws hr
  have hh : HEq (tripleLeftFlatGather R L A B D xs ys ws ≫ q)
      ((tripleFlatChart G xs ys ws ≫ G₀) ≫ q) :=
    structural_seq_heq (K:=coeff (C:=C)) e rfl rfl hl' HEq.rfl
  apply hh.trans
  apply heq_of_eq
  have hr' : tripleRightFlatGather R L A B D xs ys ws = tripleFlatChart K xs ys ws ≫ G₁ := by
    unfold tripleFlatChart
    simp only [Category.assoc]
    exact tripleRightFlatGather_chart R L NL A B D xs ys ws hl
  let k := act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => act 𝒮 Zₐ (fun z => p (x,y,z)) ws) ys) xs
  have h : G₀ ≫ q = k ≫ G₁ := tripleIndependentRaw_assoc R L P A B D xs ys ws Q
  have ht := tripleFlatChart_natural p xs ys ws
  rw [Category.assoc]
  change tripleFlatChart G xs ys ws ≫ G₀ ≫ q =
    act 𝒮 Zₐ p w ≫ tripleRightFlatGather R L A B D xs ys ws
  calc
    _ = tripleFlatChart G xs ys ws ≫ k ≫ G₁ := by rw [h]
    _ = (act 𝒮 Zₐ p w ≫ tripleFlatChart K xs ys ws) ≫ G₁ := by rw [ht, Category.assoc]
    _ = _ := by rw [Category.assoc, hr']

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
