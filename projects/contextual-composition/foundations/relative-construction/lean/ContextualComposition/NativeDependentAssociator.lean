module
public import ContextualComposition.NativeOrderedFubini
@[expose] public section

/-! The ternary dependent associator with the original ordered augmentation.
Only binary/nullary primitive linearity and the multiplicative right-unit
triangle are used to move the associator through collection. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T)

def AssocRightUnit {S : Bi (coeff (C:=C))} {Z : C} (R : Gather S T Z)
    (J : UnitCompat R I) (P : TensorPrimitive T) : Prop :=
  ∀ a b, P.assoc a b I ≫ T.map (𝟙 a) (J.ρ b) = J.ρ (T.obj a b)

variable (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P)
variable (U : AssocRightUnit R J P)

include NL Q U in
set_option backward.isDefEq.respectTransparency false in
/-- Checked continuation-first row law; there is no list-level assumption.
The term γ is the whole original continuation augmentation of this row. -/
theorem dependentAssoc_row {Y : Type u} (a b : C) (W : Y → C) (ys : List Y)
    (γ : fold 𝒮 Zₐ W ys ⟶ I) :
    (Lin.left L (T.obj a b)).collect W ys ≫ T.map (𝟙 (T.obj a b)) γ ≫ J.ρ (T.obj a b) =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫
      (Lin.left L a).collect (fun y => T.obj b (W y)) ys ≫
      T.map (𝟙 a) ((Lin.left L b).collect W ys ≫ T.map (𝟙 b) γ ≫ J.ρ b) := by
  let F := leftFactor T a
  let H := leftFactor T (T.obj a b)
  let G := leftFactor T b
  let e := fold 𝒮 Zₐ W ys
  let q := (Lin.left L b).collect W ys
  let p := (Lin.left L a).collect (fun y => T.obj b (W y)) ys
  have f : H.map γ ≫ J.ρ (T.obj a b) =
      P.assoc a b e ≫ F.map (G.map γ) ≫ F.map (J.ρ b) := by
    have g := P.assoc_nat (𝟙 a) (𝟙 b) γ
    change T.map (T.map (𝟙 a) (𝟙 b)) γ ≫ P.assoc a b I =
      P.assoc a b e ≫ F.map (G.map γ) at g
    rw [T.map_id] at g
    change T.map (𝟙 (T.obj a b)) γ ≫ P.assoc a b I = _ at g
    rw [← reassoc_of% g]
    have h : P.assoc a b I ≫ F.map (J.ρ b) = J.ρ (T.obj a b) := U a b
    rw [h]
  have g := (Q.al a b).collect W ys
  have o := Lin.collect_comp (Lin.left L b) (Lin.left L a) (NL.inner a) W ys
  change (Lin.left L (T.obj a b)).collect W ys ≫ P.assoc a b e =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫ ((Lin.left L b).comp (Lin.left L a)).collect W ys at g
  change (Lin.left L (T.obj a b)).collect W ys ≫ H.map γ ≫ J.ρ (T.obj a b) =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫ p ≫ F.map (q ≫ G.map γ ≫ J.ρ b)
  rw [f, reassoc_of% g, o, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_natural {X Y K : Type u} {A B : K → C}
    (f : X → Y → K) (ls : X → List Y) (xs : List X) (p : ∀ k, A k ⟶ B k) :
    let r := fun x => (ls x).map (f x)
    act 𝒮 Zₐ p (xs.flatMap r) ≫ taggedRaggedRows B f ls xs =
      taggedRaggedRows A f ls xs ≫ act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => p (f x y)) (ls x)) xs := by
  intro r
  let a := fun x => eqToHom (std_fold_map A (f x) (ls x))
  let b := fun x => eqToHom (std_fold_map B (f x) (ls x))
  let e := fun x => act 𝒮 Zₐ p (r x)
  let g := fun x => act 𝒮 Zₐ (fun y => p (f x y)) (ls x)
  have q (x : X) : e x ≫ b x = a x ≫ g x := (std_act_map A (f x) p (ls x)).symm
  have h : act 𝒮 Zₐ e xs ≫ act 𝒮 Zₐ b xs = act 𝒮 Zₐ a xs ≫ act 𝒮 Zₐ g xs :=
    (act_seq 𝒮 Zₐ e b xs).trans
      ((congrArg (fun u => act 𝒮 Zₐ u xs) (funext q)).trans (act_seq 𝒮 Zₐ a g xs).symm)
  unfold taggedRaggedRows
  simp only [Category.assoc]
  change act 𝒮 Zₐ p (xs.flatMap r) ≫ rowsChart B r xs ≫ act 𝒮 Zₐ b xs = _
  rw [reassoc_of% rowsChart_natural r p xs, h]

set_option backward.isDefEq.respectTransparency false in
theorem collect_taggedRaggedRows (F : C ⥤ C) [F.LaxBraided]
    {X Y K : Type u} (A : K → C) (f : X → Y → K) (ls : X → List Y) (xs : List X) :
    let K := linearFunctor F
    let r := fun x => (ls x).map (f x)
    let G := fun x => fold 𝒮 Zₐ (A ∘ f x) (ls x)
    taggedRaggedRows (F.obj ∘ A) f ls xs ≫ act 𝒮 Zₐ (fun x => K.collect (A ∘ f x) (ls x)) xs ≫ K.collect G xs =
      K.collect A (xs.flatMap r) ≫ F.map (taggedRaggedRows A f ls xs) := by
  intro K r G
  let B := fun x => fold 𝒮 Zₐ A (r x)
  let p := fun x => K.collect A (r x)
  let q := fun x => K.collect (A ∘ f x) (ls x)
  let e := fun x => std_fold_map A (f x) (ls x)
  let d := fun x => std_fold_map (F.obj ∘ A) (f x) (ls x)
  let u := fun x => eqToHom (e x)
  let v := fun x => eqToHom (d x)
  let w := fun x => F.map (u x)
  have hF {a b : C} (h : a = b) : F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
    subst b
    simp only [eqToHom_refl, F.map_id]
  have row (x : X) : v x ≫ q x = p x ≫ w x := by
    unfold w u
    rw [hF]
    exact (heq_paste (d x) (congrArg F.obj (e x))
      (linCollect_map_heq K A (f x) (ls x)).symm).symm
  have row' : act 𝒮 Zₐ v xs ≫ act 𝒮 Zₐ q xs = act 𝒮 Zₐ p xs ≫ act 𝒮 Zₐ w xs :=
    (act_seq 𝒮 Zₐ v q xs).trans
      ((congrArg (fun z => act 𝒮 Zₐ z xs) (funext row)).trans (act_seq 𝒮 Zₐ p w xs).symm)
  have nt : act 𝒮 Zₐ w xs ≫ K.collect G xs = K.collect B xs ≫ F.map (act 𝒮 Zₐ u xs) :=
    collect_map_naturality F u xs
  have ht : rowsChart (F.obj ∘ A) r xs ≫ act 𝒮 Zₐ p xs ≫ K.collect B xs =
      K.collect A (xs.flatMap r) ≫ F.map (rowsChart A r xs) :=
    collect_rows F A r xs
  unfold taggedRaggedRows
  simp only [Category.assoc]
  change rowsChart (F.obj ∘ A) r xs ≫ act 𝒮 Zₐ v xs ≫ act 𝒮 Zₐ q xs ≫ K.collect G xs =
    K.collect A (xs.flatMap r) ≫ F.map (rowsChart A r xs ≫ act 𝒮 Zₐ u xs)
  rw [reassoc_of% row', nt, F.map_comp, reassoc_of% ht]

include NL Q U in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem dependentAssoc_middle {Y W : Type u} (a : C) (B : Y → C) (D : Y → W → C)
    (ys : List Y) (ws : Y → List W)
    (δ : fold 𝒮 Zₐ B ys ⟶ I) (γ : ∀ y, fold 𝒮 Zₐ (D y) (ws y) ⟶ I)
    [(leftFactor T a).LaxBraided] (hl : SameLeftGather T a L) :
    let A₀ := fun k : Y × W => T.obj (T.obj a (B k.1)) (D k.1 k.2)
    let A₁ := dependentLabels (T:=T) B D
    let F := leftFactor T a
    let al := fun k : Y × W => P.assoc a (B k.1) (D k.1 k.2)
    let c := fun y => (Lin.left L (T.obj a (B y))).collect (D y) (ws y) ≫
      T.map (𝟙 (T.obj a (B y))) (γ y) ≫ J.ρ (T.obj a (B y))
    taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ c ys ≫
      (Lin.left L a).collect B ys ≫ F.map δ ≫ J.ρ a =
    act 𝒮 Zₐ al (dependentWord ys ws) ≫ (Lin.left L a).collect A₁ (dependentWord ys ws) ≫
      F.map (dependentWordAugCell R L J ys ws B D (indexedAugmentation γ) δ) ≫ J.ρ a := by
  intro A₀ A₁ F al c
  let K := Lin.left L a
  let A₂ := fun k => F.obj (A₁ k)
  let B₀ := fun y => fold 𝒮 Zₐ (A₁ ∘ Prod.mk y) (ws y)
  let e := fun y => act 𝒮 Zₐ (fun w => al (y,w)) (ws y)
  let f := fun y => K.collect (A₁ ∘ Prod.mk y) (ws y)
  let q := fun y => (Lin.left L (B y)).collect (D y) (ws y) ≫ T.map (𝟙 (B y)) (γ y) ≫ J.ρ (B y)
  have h (y : Y) : c y = e y ≫ f y ≫ F.map (q y) :=
    dependentAssoc_row R L J P NL Q U a (B y) (D y) (ws y) (γ y)
  have g : act 𝒮 Zₐ c ys = act 𝒮 Zₐ e ys ≫ act 𝒮 Zₐ f ys ≫ act 𝒮 Zₐ (fun y => F.map (q y)) ys := by
    have e₁ := act_seq 𝒮 Zₐ e (fun y => f y ≫ F.map (q y)) ys
    have e₂ := act_seq 𝒮 Zₐ f (fun y => F.map (q y)) ys
    exact (congrArg (fun v => act 𝒮 Zₐ v ys) (funext h)).trans
      (e₁.symm.trans (congrArg (fun v => act 𝒮 Zₐ e ys ≫ v) e₂.symm))
  have j : act 𝒮 Zₐ (fun y => F.map (q y)) ys ≫ K.collect B ys =
      K.collect B₀ ys ≫ F.map (act 𝒮 Zₐ q ys) := Lin.collect_nat K (NL.inner a) q ys
  have hs : taggedRaggedRows A₂ Prod.mk ws ys ≫ act 𝒮 Zₐ f ys ≫ K.collect B₀ ys =
      K.collect A₁ (dependentWord ys ws) ≫ F.map (taggedRaggedRows A₁ Prod.mk ws ys) := by
    let F' := linearFunctor F
    have h₁ : (fun y => F'.collect (A₁ ∘ Prod.mk y) (ws y)) = f :=
      funext fun y => leftFactor_sameCollect T a L hl _ _
    have h₂ := leftFactor_sameCollect T a L hl B₀ ys
    have h₃ := leftFactor_sameCollect T a L hl A₁ (dependentWord ys ws)
    have k := collect_taggedRaggedRows F A₁ Prod.mk ws ys
    change taggedRaggedRows A₂ Prod.mk ws ys ≫ act 𝒮 Zₐ (fun y => F'.collect (A₁ ∘ Prod.mk y) (ws y)) ys ≫
        F'.collect B₀ ys = F'.collect A₁ (dependentWord ys ws) ≫ _ at k
    rw [h₁, h₂, h₃] at k
    exact k
  have hw : act 𝒮 Zₐ al (dependentWord ys ws) ≫ taggedRaggedRows A₂ Prod.mk ws ys =
      taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ e ys :=
    taggedRaggedRows_natural Prod.mk ws ys al
  have h₀ : dependentWordAugCell R L J ys ws B D (indexedAugmentation γ) δ =
      taggedRaggedRows A₁ Prod.mk ws ys ≫ act 𝒮 Zₐ q ys ≫ δ :=
    dependentWordAug_raw_rows R L J ys ws B D γ δ
  rw [h₀, g]
  simp only [Category.assoc, F.map_comp]
  change taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ e ys ≫ act 𝒮 Zₐ f ys ≫
      act 𝒮 Zₐ (fun y => F.map (q y)) ys ≫ K.collect B ys ≫ F.map δ ≫ J.ρ a =
    act 𝒮 Zₐ al (dependentWord ys ws) ≫ K.collect A₁ (dependentWord ys ws) ≫
      F.map (taggedRaggedRows A₁ Prod.mk ws ys) ≫ F.map (act 𝒮 Zₐ q ys) ≫ F.map δ ≫ J.ρ a
  rw [← reassoc_of% hw, reassoc_of% j, reassoc_of% hs]

def tripleRetag {X Y W : Type u} : ((X × Y) × W) ≃ X × Y × W where
  toFun t := (t.1.1,t.1.2,t.2)
  invFun t := ((t.1,t.2.1),t.2.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem tripleRetag_word {X Y W : Type u} (xs : List X) (ys : X → List Y) (ws : X → Y → List W) :
    (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)).map tripleRetag =
      dependentWord xs (fun x => dependentWord (ys x) (ws x)) := by
  unfold dependentWord
  simp only [List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map]
  rfl

theorem tripleWord_flat {X Y W : Type u} (xs : List X) (ys : X → List Y) (ws : X → Y → List W) :
    dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2) =
      xs.flatMap (fun x => (dependentWord (ys x) (ws x)).map (fun z => ((x,z.1),z.2))) := by
  unfold dependentWord
  simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem nestedDependentRows {X Y W : Type u}
    (A : (X × Y) × W → C) (B : X × Y → C)
    (xs : List X) (ys : X → List Y) (ws : X → Y → List W)
    (p : ∀ t : X × Y, fold 𝒮 Zₐ (A ∘ Prod.mk t) (ws t.1 t.2) ⟶ B t) :
    let zs := dependentWord xs ys
    let es := fun x => dependentWord (ys x) (ws x)
    let f := fun (x : X) (t : Y × W) => ((x,t.1),t.2)
    taggedRaggedRows A Prod.mk (fun t => ws t.1 t.2) zs ≫ act 𝒮 Zₐ p zs ≫
      taggedRaggedRows B Prod.mk ys xs =
    eqToHom (congrArg (fold 𝒮 Zₐ A) (tripleWord_flat xs ys ws)) ≫
      taggedRaggedRows A f es xs ≫
        act 𝒮 Zₐ (fun x => taggedRaggedRows (A ∘ f x) Prod.mk (ws x) (ys x) ≫
          act 𝒮 Zₐ (fun y => p (x,y)) (ys x)) xs := by
  intro zs es f
  let rows := fun x => (ys x).map (Prod.mk x)
  let ls := fun (t : X × Y) => ws t.1 t.2
  let G := fold 𝒮 Zₐ A
  let M := fun t => (ls t).map (Prod.mk t)
  let H := fun x => (rows x).flatMap M
  let H' := fun x => (es x).map (f x)
  let g := fun x => std_fold_map B (Prod.mk x) (ys x)
  let c := fun x => taggedRaggedRows A Prod.mk ls (rows x) ≫ act 𝒮 Zₐ p (rows x)
  let d := fun x => taggedRaggedRows (A ∘ f x) Prod.mk (ws x) (ys x) ≫
    act 𝒮 Zₐ (fun y => p (x,y)) (ys x)
  have l (x : X) : H x = H' x := by
    unfold H H' rows M ls es dependentWord
    rw [List.flatMap_map, List.map_flatMap]
    congr 1
    funext y
    rw [List.map_map]
    rfl
  let v := fun x => congrArg G (l x)
  let e := fun x => std_fold_map A (f x) (es x)
  have h (x : X) : c x ≫ eqToHom (g x) = eqToHom (v x) ≫ eqToHom (e x) ≫ d x := by
    let rr := fun (x : X) (y : Y) (w : W) => ((x,y),w)
    let j := fun x => List.flatMap_map (Prod.mk x) M (ys x)
    let m := fun x => (ys x).flatMap (fun y => (ws x y).map (rr x y))
    have n (x : X) : (es x).map (f x) = m x := by
      unfold es m dependentWord
      rw [List.map_flatMap]
      congr 1
      funext y
      rw [List.map_map]
      rfl
    let y := fun x => taggedRaggedRows A (rr x) (ws x) (ys x)
    let u := fun x => taggedRaggedRows (A ∘ f x) Prod.mk (ws x) (ys x)
    let b := fun x => act 𝒮 Zₐ (fun y => p (x,y)) (ys x)
    have a : c x ≫ eqToHom (g x) = eqToHom (congrArg G (j x)) ≫ y x ≫ b x := by
      have a₀ := taggedRaggedRows_read_parents A B Prod.mk ls (Prod.mk x) (ys x) p
      dsimp only at a₀
      simpa only [c, y, b, rows, rr, ls, Function.comp_def, Category.assoc] using a₀
    have a' : y x = eqToHom ((congrArg G (n x)).symm.trans (e x)) ≫ u x := by
      have k := heq_paste ((congrArg G (n x)).symm.trans (e x)) (rfl : _ = _)
        (taggedRaggedRows_tag_heq A (f x) Prod.mk (ws x) (ys x)).symm
      rw [eqToHom_refl, Category.comp_id] at k
      exact k
    rw [a, a']
    change eqToHom (congrArg G (j x)) ≫ (eqToHom ((congrArg G (n x)).symm.trans (e x)) ≫ u x) ≫ b x =
      eqToHom (v x) ≫ eqToHom (e x) ≫ (u x ≫ b x)
    simp only [Category.assoc, eqToHom_trans_assoc]
  have g₀ := taggedRaggedRows_parent_groups A B Prod.mk ls xs rows p
  let e₀ : zs.flatMap M = xs.flatMap H := List.flatMap_assoc
  have gg : act 𝒮 Zₐ c xs ≫ act 𝒮 Zₐ (fun x => eqToHom (g x)) xs =
      act 𝒮 Zₐ (fun x => eqToHom (v x)) xs ≫ act 𝒮 Zₐ (fun x => eqToHom (e x)) xs ≫ act 𝒮 Zₐ d xs :=
    (act_seq 𝒮 Zₐ c (fun x => eqToHom (g x)) xs).trans
      ((congrArg (fun w => act 𝒮 Zₐ w xs) (funext h)).trans
        ((act_seq 𝒮 Zₐ (fun x => eqToHom (v x)) (fun x => eqToHom (e x) ≫ d x) xs).symm.trans
          (congrArg (fun m => act 𝒮 Zₐ (fun x => eqToHom (v x)) xs ≫ m)
            (act_seq 𝒮 Zₐ (fun x => eqToHom (e x)) d xs).symm)))
  have h₁ : rowsChart A H xs ≫ act 𝒮 Zₐ (fun x => eqToHom (v x)) xs =
      eqToHom (congrArg G (congrArg (fun g => xs.flatMap g) (funext l))) ≫ rowsChart A H' xs :=
    rowsChart_rows_congr A l xs
  change (taggedRaggedRows A Prod.mk ls (xs.flatMap rows) ≫ act 𝒮 Zₐ p (xs.flatMap rows) ≫
    rowsChart B rows xs ≫ act 𝒮 Zₐ (fun x => eqToHom (g x)) xs) = _
  rw [reassoc_of% g₀, gg, reassoc_of% h₁]
  unfold d taggedRaggedRows
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

section Global
variable {X Y W : Type u}
variable (xs : List X) (ys : X → List Y) (ws : X → Y → List W)
variable (V : X → C) (B : X → Y → C) (D : X → Y → W → C)
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I)
variable (γ : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ I)

def assocLeftLabels (T : Bi (coeff (C:=C))) (V : X → C) (B : X → Y → C) (D : X → Y → W → C) :
    (X × Y) × W → C :=
  fun z => T.obj (T.obj (V z.1.1) (B z.1.1 z.1.2)) (D z.1.1 z.1.2 z.2)

def assocRightLabels (T : Bi (coeff (C:=C))) (V : X → C) (B : X → Y → C) (D : X → Y → W → C) :
    X × Y × W → C :=
  fun z => T.obj (V z.1) (T.obj (B z.1 z.2.1) (D z.1 z.2.1 z.2.2))

def dependentAssocLeftAug :
    fold 𝒮 Zₐ (assocLeftLabels T V B D) (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)) ⟶ I :=
  dependentWordAugCell R L J (dependentWord xs ys) (fun p => ws p.1 p.2)
    (dependentLabels (T:=T) V B) (fun p => D p.1 p.2)
    (indexedAugmentation (fun p => γ p.1 p.2))
    (dependentWordAugCell R L J xs ys V B (indexedAugmentation δ) ε)

def dependentAssocRightAug :
    fold 𝒮 Zₐ (assocRightLabels T V B D) (dependentWord xs (fun x => dependentWord (ys x) (ws x))) ⟶ I :=
  dependentWordAugCell R L J xs (fun x => dependentWord (ys x) (ws x)) V
    (fun x => dependentLabels (T:=T) (B x) (D x))
    (indexedAugmentation (fun x => dependentWordAugCell R L J (ys x) (ws x) (B x) (D x)
      (indexedAugmentation (γ x)) (δ x))) ε

include NL Q U in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem dependentAssoc_augmentation
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L) :
    let A₀ := assocLeftLabels T V B D
    let A₀' := A₀ ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
    let w₀ := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
    let w₁ := dependentWord xs (fun x => dependentWord (ys x) (ws x))
    let p := fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2)
    let pin : fold 𝒮 Zₐ A₀ w₀ = fold 𝒮 Zₐ A₀' w₁ :=
      (std_fold_map A₀' tripleRetag w₀).symm.trans (congrArg (fold 𝒮 Zₐ A₀') (tripleRetag_word xs ys ws))
    dependentAssocLeftAug R L J xs ys ws V B D ε δ γ =
      eqToHom pin ≫ act 𝒮 Zₐ p w₁ ≫ dependentAssocRightAug R L J xs ys ws V B D ε δ γ := by
  intro A₀ A₀' w₀ w₁ p pin
  let A₁ := assocRightLabels T V B D
  let X₀ := dependentLabels (T:=T) V B
  let zs := dependentWord xs ys
  let b := fun x => dependentWord (ys x) (ws x)
  let lt := fun (x : X) (v : Y × W) => ((x,v.1),v.2)
  let rt := fun (x : X) (v : Y × W) => (x,v)
  let L₀ := fun (v : X × Y) =>
    (Lin.left L (X₀ v)).collect (D v.1 v.2) (ws v.1 v.2) ≫ T.map (𝟙 (X₀ v)) (γ v.1 v.2) ≫ J.ρ (X₀ v)
  let a := fun x => (Lin.left L (V x)).collect (B x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let c := fun x => dependentWordAugCell R L J (ys x) (ws x) (B x) (D x) (indexedAugmentation (γ x)) (δ x)
  let a' := fun x => (Lin.left L (V x)).collect (dependentLabels (T:=T) (B x) (D x)) (b x) ≫
    T.map (𝟙 (V x)) (c x) ≫ J.ρ (V x)
  have h₀ : dependentAssocLeftAug R L J xs ys ws V B D ε δ γ =
      taggedRaggedRows A₀ Prod.mk (fun v => ws v.1 v.2) zs ≫ act 𝒮 Zₐ L₀ zs ≫
      taggedRaggedRows X₀ Prod.mk ys xs ≫ act 𝒮 Zₐ a xs ≫ ε := by
    have k₀ := dependentWordAug_raw_rows R L J zs (fun (v : X × Y) => ws v.1 v.2) X₀
      (fun v => D v.1 v.2) (fun v => γ v.1 v.2)
      (dependentWordAugCell R L J xs ys V B (indexedAugmentation δ) ε)
    have k₁ : dependentWordAugCell R L J xs ys V B (indexedAugmentation δ) ε = _ :=
      dependentWordAug_raw_rows R L J xs ys V B δ ε
    change _ = taggedRaggedRows A₀ Prod.mk (fun v => ws v.1 v.2) zs ≫ act 𝒮 Zₐ L₀ zs ≫
      dependentWordAugCell R L J xs ys V B (indexedAugmentation δ) ε at k₀
    exact k₀.trans (congrArg (fun k => taggedRaggedRows A₀ Prod.mk (fun v => ws v.1 v.2) zs ≫ act 𝒮 Zₐ L₀ zs ≫ k) k₁)
  have h₁ : dependentAssocRightAug R L J xs ys ws V B D ε δ γ =
      taggedRaggedRows A₁ rt b xs ≫ act 𝒮 Zₐ a' xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs b V (fun x => dependentLabels (T:=T) (B x) (D x)) c ε
  let t := fun x => taggedRaggedRows (A₀ ∘ lt x) Prod.mk (ws x) (ys x) ≫
     act 𝒮 Zₐ (fun y => L₀ (x,y)) (ys x)
  let r := fun x => act 𝒮 Zₐ (fun y => p (rt x y)) (b x)
  have h₂ (x : X) : t x ≫ a x = r x ≫ a' x :=
    (Category.assoc _ _ _).trans (dependentAssoc_middle R L J P NL Q U (V x)
      (B x) (D x) (ys x) (ws x) (δ x) (γ x) (hl (V x)))
  have hh : act 𝒮 Zₐ t xs ≫ act 𝒮 Zₐ a xs = act 𝒮 Zₐ r xs ≫ act 𝒮 Zₐ a' xs :=
    (act_seq 𝒮 Zₐ t a xs).trans ((congrArg (fun f => act 𝒮 Zₐ f xs) (funext h₂)).trans
      (act_seq 𝒮 Zₐ r a' xs).symm)
  let fp := congrArg (fold 𝒮 Zₐ A₀) (tripleWord_flat xs ys ws)
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let pp := taggedRaggedRows A₀ lt b xs
  let qq := taggedRaggedRows A₀' rt b xs
  have qqpin : fold 𝒮 Zₐ A₀' w₁ = fold 𝒮 Zₐ A₀ (xs.flatMap (fun x => (b x).map (lt x))) := pin.symm.trans fp
  have ht : qq = eqToHom qqpin ≫ pp := by
    have k := taggedRaggedRows_tag_heq A₀ g.symm rt b xs
    have q := heq_paste qqpin (rfl : _ = _) k
    rw [eqToHom_refl, Category.comp_id] at q
    exact q
  have ho : eqToHom pin ≫ qq = eqToHom fp ≫ pp := by
    rw [ht, eqToHom_trans_assoc]
  have zz : act 𝒮 Zₐ p w₁ ≫ taggedRaggedRows A₁ rt b xs = qq ≫ act 𝒮 Zₐ r xs :=
    taggedRaggedRows_natural rt b xs p
  rw [h₀, h₁, reassoc_of% nestedDependentRows, reassoc_of% hh, reassoc_of% zz, reassoc_of% ho]

noncomputable def dependentAssocLeft :
    Aug ℙ I :=
  wordAug (assocLeftLabels T V B D) (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2))
    (dependentAssocLeftAug R L J xs ys ws V B D ε δ γ)

noncomputable def dependentAssocRight :
    Aug ℙ I :=
  wordAug (assocRightLabels T V B D) (dependentWord xs (fun x => dependentWord (ys x) (ws x)))
    (dependentAssocRightAug R L J xs ys ws V B D ε δ γ)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The literal dependent associator at fixed augmented input, with the
actual tensor associator acting on each raw triple of branch addresses. -/
noncomputable def dependentAssocIso
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (ι : ∀ a b c, IsIso (P.assoc a b c))
    (hn : (dependentWord xs (fun x => dependentWord (ys x) (ws x))).Nodup) :
    NativeAugmentedIso (dependentAssocLeft R L J xs ys ws V B D ε δ γ)
      (dependentAssocRight R L J xs ys ws V B D ε δ γ) := by
  let A₀ := assocLeftLabels T V B D
  let A₁ := assocRightLabels T V B D
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let A := A₀ ∘ g.symm
  let w₀ := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
  let w₁ := dependentWord xs (fun x => dependentWord (ys x) (ws x))
  let p := dependentAssocLeftAug R L J xs ys ws V B D ε δ γ
  let q := dependentAssocRightAug R L J xs ys ws V B D ε δ γ
  let e : w₀.map g = w₁ := tripleRetag_word xs ys ws
  let pin : fold 𝒮 Zₐ A₀ w₀ = fold 𝒮 Zₐ A w₁ :=
    (std_fold_map A g w₀).symm.trans (congrArg (fold 𝒮 Zₐ A) e)
  let p' := eqToHom pin.symm ≫ p
  let φ (v : X × Y × W) : A v ≅ A₁ v := by
    let _ := ι (V v.1) (B v.1 v.2.1) (D v.1 v.2.1 v.2.2)
    exact asIso (P.assoc (V v.1) (B v.1 v.2.1) (D v.1 v.2.1 v.2.2))
  have h := dependentAssoc_augmentation R L J P NL Q U xs ys ws V B D ε δ γ hl
  have h' : p = eqToHom pin ≫ act 𝒮 Zₐ (fun v => (φ v).hom) w₁ ≫ q := h
  have hp : AddressOrder.mapSum additiveStructure A (.ident w₁) ≫
      act 𝒮 Zₐ (fun v => (φ v).hom) w₁ ≫ q = p' := by
    change 𝟙 _ ≫ act 𝒮 Zₐ (fun v => (φ v).hom) w₁ ≫ q = eqToHom pin.symm ≫ p
    rw [h', eqToHom_trans_assoc, eqToHom_refl]
  have hz : dependentAssocLeft R L J xs ys ws V B D ε δ γ = wordAug A w₁ p' :=
    wordAug_read_eq A g w₀ w₁ e _ _ (hom_source_pin_heq pin.symm p).symm
  exact (wordAugIso A A₁ (.ident w₁) hn φ p' q hp).retarget hz.symm rfl

set_option backward.isDefEq.respectTransparency false in
theorem dependentAssocIso_addr
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (ι : ∀ a b c, IsIso (P.assoc a b c))
    (hn : (dependentWord xs (fun x => dependentWord (ys x) (ws x))).Nodup)
    (i : Fin (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)).length) :
    let e := dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι hn
    (dependentWord xs (fun x => dependentWord (ys x) (ws x)))[e.hom.native.addr i] =
      tripleRetag ((dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2))[i]) := by
  intro e
  let w₀ := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
  let w₁ := dependentWord xs (fun x => dependentWord (ys x) (ws x))
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let h := tripleRetag_word xs ys ws
  let k := Fin.cast ((List.length_map g).symm.trans (congrArg List.length h)) i
  let p := (AddressOrder.ident w₁).perm
  have q : e.hom.native.addr i = wordEquiv p hn k := by
    unfold e dependentAssocIso
    dsimp only
    rw [NativeAugmentedIso.retarget_addr]
    rfl
  have h₀ := congrArg (fun i : Fin w₁.length => w₁[i]) q
  exact h₀.trans ((wordEquiv_get p hn k).trans (retag_word_get g w₀ h i).symm)

end Global

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
set_option linter.style.haveILetI false in
theorem standardAssocRightUnit (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom) :
    AssocRightUnit r j (@tensorPrimitives C cat mul br) := by
  intro a b
  rw [h b, h _]
  letI := mul
  change (α_ a b (𝟙_ C)).hom ≫ (𝟙 a ⊗ₘ (ρ_ b).hom) = (ρ_ (a ⊗ b)).hom
  rw [id_tensorHom]
  exact (rightUnitor_tensor_hom a b).symm


end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
