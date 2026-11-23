module
public import ContextualComposition.NativeSingletonStructural
@[expose] public section

/-! Transporting actual dependent augmentations along pointwise
structural maps in a common ordered raw chart. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (NL : GatherLeftNat L)

set_option backward.isDefEq.respectTransparency false in
include NL in
theorem dependentRow_pointwise {Y : Type u} {a b : C} {V W : Y → C} (ys : List Y)
    (p : a ⟶ b) (q : ∀ y, V y ⟶ W y)
    (δ : fold 𝒮 Zₐ V ys ⟶ I) (η : fold 𝒮 Zₐ W ys ⟶ I)
    (h : act 𝒮 Zₐ q ys ≫ η = δ) :
    act 𝒮 Zₐ (fun y => T.map p (q y)) ys ≫
        (Lin.left L b).collect W ys ≫ T.map (𝟙 b) η ≫ J.ρ b =
      (Lin.left L a).collect V ys ≫ T.map (𝟙 a) δ ≫ J.ρ a ≫ p := by
  let F := leftFactor T a
  let G := leftFactor T b
  let r := fun y => T.map p (𝟙 (W y))
  let s := fun y => F.map (q y)
  have fac (y : Y) : T.map p (q y) = s y ≫ r y := by
    have w := T.map_seq (𝟙 a) p (q y) (𝟙 (W y))
    change T.map (𝟙 a ≫ p) (q y ≫ 𝟙 (W y)) = _ at w
    rw [Category.id_comp, Category.comp_id] at w
    exact w
  have h₁ : act 𝒮 Zₐ (fun y => T.map p (q y)) ys = act 𝒮 Zₐ s ys ≫ act 𝒮 Zₐ r ys :=
    (congrArg (fun z => act 𝒮 Zₐ z ys) (funext fac)).trans (act_seq 𝒮 Zₐ s r ys).symm
  have h₂ : act 𝒮 Zₐ r ys ≫ (Lin.left L b).collect W ys =
      (Lin.left L a).collect W ys ≫ T.map p (𝟙 _) := (NL.outer p).collect W ys |>.symm
  have h₃ : act 𝒮 Zₐ s ys ≫ (Lin.left L a).collect W ys =
      (Lin.left L a).collect V ys ≫ F.map (act 𝒮 Zₐ q ys) := Lin.collect_nat _ (NL.inner a) q ys
  have h₄ : T.map p (𝟙 (fold 𝒮 Zₐ W ys)) ≫ G.map η = F.map η ≫ T.map p (𝟙 I) := by
    have t₁ := T.map_seq p (𝟙 b) (𝟙 (fold 𝒮 Zₐ W ys)) η
    have t₂ := T.map_seq (𝟙 a) p η (𝟙 I)
    change T.map (p ≫ 𝟙 b) (𝟙 _ ≫ η) = _ at t₁
    change T.map (𝟙 a ≫ p) (η ≫ 𝟙 I) = _ at t₂
    rw [Category.comp_id, Category.id_comp] at t₁
    rw [Category.id_comp, Category.comp_id] at t₂
    exact t₁.symm.trans t₂
  have h₅ : T.map p (𝟙 I) ≫ J.ρ b = J.ρ a ≫ p := J.natural p
  change act 𝒮 Zₐ (fun y => T.map p (q y)) ys ≫
    (Lin.left L b).collect W ys ≫ G.map η ≫ J.ρ b = _
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅, ← reassoc_of% F.map_comp, h]

include NL in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem dependentAug_pointwise {X Y : Type u}
    {V V' : X → C} {W W' : X → Y → C}
    (xs : List X) (ys : X → List Y) (p : ∀ x, V x ⟶ V' x)
    (q : ∀ x y, W x y ⟶ W' x y)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (ε' : fold 𝒮 Zₐ V' xs ⟶ I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (δ' : ∀ x, fold 𝒮 Zₐ (W' x) (ys x) ⟶ I)
    (hp : act 𝒮 Zₐ p xs ≫ ε' = ε)
    (hq : ∀ x, act 𝒮 Zₐ (q x) (ys x) ≫ δ' x = δ x) :
    act 𝒮 Zₐ (fun z : X × Y => T.map (p z.1) (q z.1 z.2)) (dependentWord xs ys) ≫
      dependentWordAugCell R L J xs ys V' W' (indexedAugmentation δ') ε' =
    dependentWordAugCell R L J xs ys V W (indexedAugmentation δ) ε := by
  let A := dependentLabels (T:=T) V W
  let B := dependentLabels (T:=T) V' W'
  let z := fun k : X × Y => T.map (p k.1) (q k.1 k.2)
  let q₀ := fun x => act 𝒮 Zₐ (fun y => z (x,y)) (ys x)
  let d := fun x => (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let e := fun x => (Lin.left L (V' x)).collect (W' x) (ys x) ≫ T.map (𝟙 (V' x)) (δ' x) ≫ J.ρ (V' x)
  have g : act 𝒮 Zₐ z (dependentWord xs ys) ≫ taggedRaggedRows B Prod.mk ys xs =
      taggedRaggedRows A Prod.mk ys xs ≫ act 𝒮 Zₐ q₀ xs := taggedRaggedRows_natural Prod.mk ys xs z
  have h (x : X) : q₀ x ≫ e x = d x ≫ p x := by
    unfold d
    simp only [Category.assoc]
    exact dependentRow_pointwise R L J NL (ys x) (p x) (q x) (δ x) (δ' x) (hq x)
  have h' : act 𝒮 Zₐ q₀ xs ≫ act 𝒮 Zₐ e xs = act 𝒮 Zₐ d xs ≫ act 𝒮 Zₐ p xs :=
    (act_seq 𝒮 Zₐ q₀ e xs).trans
      ((congrArg (fun f => act 𝒮 Zₐ f xs) (funext h)).trans (act_seq 𝒮 Zₐ d p xs).symm)
  have x : dependentWordAugCell R L J xs ys V W (indexedAugmentation δ) ε =
      taggedRaggedRows A Prod.mk ys xs ≫ act 𝒮 Zₐ d xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs ys V W δ ε
  have y : dependentWordAugCell R L J xs ys V' W' (indexedAugmentation δ') ε' =
      taggedRaggedRows B Prod.mk ys xs ≫ act 𝒮 Zₐ e xs ≫ ε' :=
    dependentWordAug_raw_rows R L J xs ys V' W' δ' ε'
  rw [x,y, reassoc_of% g, reassoc_of% h', hp]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
/-- Arbitrary order-preserving retag of continuation words, fixing the
parent alphabet. The whole augmentation is transported, not split. -/
theorem dependentAug_child_retag {X Y W : Type u}
    (xs : List X) (ys : X → List Y) (ws : X → List W)
    (V : X → C) (A : X → W → C) (f : X → Y → W)
    (h : ∀ x, (ys x).map (f x) = ws x)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (A x) (ws x) ⟶ I) :
    let A₀ := fun x => A x ∘ f x
    let e := fun x => (std_fold_map (A x) (f x) (ys x)).symm.trans (congrArg (fold 𝒮 Zₐ (A x)) (h x))
    let δ₀ := fun x => eqToHom (e x) ≫ δ x
    HEq (dependentWordAugCell R L J xs ys V A₀ (indexedAugmentation δ₀) ε)
      (dependentWordAugCell R L J xs ws V A (indexedAugmentation δ) ε) := by
  intro A₀ e δ₀
  let B := dependentLabels (T:=T) V A
  let g := fun t : X × Y => (t.1,f t.1 t.2)
  let r := fun x => T.obj (V x)
  let p := fun x => (Lin.left L (V x)).collect (A₀ x) (ys x) ≫ T.map (𝟙 (V x)) (δ₀ x) ≫ J.ρ (V x)
  let q := fun x => (Lin.left L (V x)).collect (A x) (ws x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let c := fun x => (congrArg (fold 𝒮 Zₐ (r x ∘ A x)) (h x).symm).trans
    (std_fold_map (r x ∘ A x) (f x) (ys x))
  let H := fun x => fold 𝒮 Zₐ (r x ∘ A₀ x) (ys x)
  have k (x : X) : eqToHom (c x) ≫ p x = q x := by
    let F := Lin.left L (V x)
    let G := leftFactor T (V x)
    have v : HEq (F.collect (A x) (ws x)) (F.collect (A₀ x) (ys x)) := by
      have z {u : List W} (d : u = ws x) :
          HEq (F.collect (A x) (ws x)) (F.collect (A x) u) := by subst u; rfl
      exact (z (h x)).trans (linCollect_map_heq F (A x) (f x) (ys x)).symm
    have v' := heq_paste (c x) (congrArg (r x) (e x).symm) v
    have h' {a b : C} (d : a = b) : G.map (eqToHom d) = eqToHom (congrArg G.obj d) := by
      subst b
      simp only [eqToHom_refl, G.map_id]
    have k' : eqToHom (congrArg (r x) (e x).symm) ≫ G.map (δ₀ x) = G.map (δ x) := by
      change eqToHom (congrArg G.obj (e x).symm) ≫ G.map (eqToHom (e x) ≫ δ x) = _
      rw [G.map_comp, h', reassoc_of% eqToHom_trans, eqToHom_refl, Category.id_comp]
    change eqToHom (c x) ≫ F.collect (A₀ x) (ys x) ≫ G.map (δ₀ x) ≫ J.ρ (V x) =
      F.collect (A x) (ws x) ≫ G.map (δ x) ≫ J.ρ (V x)
    rw [← reassoc_of% v', reassoc_of% k']
  have k' : act 𝒮 Zₐ (fun x => eqToHom (c x)) xs ≫ act 𝒮 Zₐ p xs = act 𝒮 Zₐ q xs :=
    (act_seq 𝒮 Zₐ (fun x => eqToHom (c x)) p xs).trans (congrArg (fun z => act 𝒮 Zₐ z xs) (funext k))
  have p₀ : dependentWordAugCell R L J xs ys V A₀ (indexedAugmentation δ₀) ε =
      taggedRaggedRows (B ∘ g) Prod.mk ys xs ≫ act 𝒮 Zₐ p xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs ys V A₀ δ₀ ε
  have p₁ : dependentWordAugCell R L J xs ws V A (indexedAugmentation δ) ε =
      taggedRaggedRows B Prod.mk ws xs ≫ act 𝒮 Zₐ q xs ≫ ε :=
    dependentWordAug_raw_rows R L J xs ws V A δ ε
  let l := fun x => (ys x).map (fun y => (x,f x y))
  let z := congrArg (fold 𝒮 Zₐ B) (congrArg (fun l => xs.flatMap l)
    (funext fun x => (congrArg (List.map (Prod.mk x)) (h x).symm).trans List.map_map))
  have b := taggedRaggedRows_childRead B Prod.mk f ys ws h xs
  change taggedRaggedRows B Prod.mk ws xs ≫ act 𝒮 Zₐ (fun x => eqToHom (c x)) xs =
    eqToHom z ≫ taggedRaggedRows B (fun x y => (x,f x y)) ys xs at b
  rw [p₀,p₁]
  have a := taggedRaggedRows_tag_heq B g Prod.mk ys xs
  have w : (dependentWord xs ys).map g = xs.flatMap l := by
    unfold dependentWord
    simp only [List.map_flatMap, List.map_map]
    rfl
  let e₀ := (std_fold_map B g (dependentWord xs ys)).symm.trans (congrArg (fold 𝒮 Zₐ B) w)
  have j : eqToHom z ≫ (taggedRaggedRows B (fun x y => (x,f x y)) ys xs ≫ act 𝒮 Zₐ p xs ≫ ε) =
      taggedRaggedRows B Prod.mk ws xs ≫ act 𝒮 Zₐ q xs ≫ ε := by
    rw [← reassoc_of% b, reassoc_of% k']
  have v : HEq (taggedRaggedRows (B ∘ g) Prod.mk ys xs ≫ act 𝒮 Zₐ p xs ≫ ε)
      (taggedRaggedRows B (fun x y => (x,f x y)) ys xs ≫ act 𝒮 Zₐ p xs ≫ ε) :=
    structural_seq_heq (K:=coeff (C:=C)) e₀ (rfl : fold 𝒮 Zₐ H xs = _) (rfl : I = _) a HEq.rfl
  exact v.trans ((hom_source_pin_heq z _).symm.trans (heq_of_eq j))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
/-- Retag the parent word along its exact address reading. Declared
continuation words are read at the matching parent, not reindexed
through an equality of coefficient values. -/
theorem dependentAug_parent_retag {X X' Y : Type u}
    (xs : List X) (xs' : List X') (ys : X' → List Y)
    (V : X' → C) (A : X' → Y → C) (f : X → X') (h : xs.map f = xs')
    (ε : fold 𝒮 Zₐ V xs' ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (A x) (ys x) ⟶ I) :
    let e := (std_fold_map V f xs).symm.trans (congrArg (fold 𝒮 Zₐ V) h)
    HEq
      (dependentWordAugCell R L J xs (ys ∘ f) (V ∘ f) (A ∘ f)
        (indexedAugmentation (fun x => δ (f x))) (eqToHom e ≫ ε))
      (dependentWordAugCell R L J xs' ys V A (indexedAugmentation δ) ε) := by
  subst xs'
  intro e
  let B := dependentLabels (T:=T) V A
  let g := fun t : X × Y => (f t.1,t.2)
  let p := fun x => (Lin.left L (V x)).collect (A x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)
  let w := dependentWord xs (ys ∘ f)
  let M := fun x => (ys x).map (Prod.mk x)
  let z := congrArg (fold 𝒮 Zₐ B) (List.flatMap_map f M xs)
  let u := std_fold_map V f xs
  have h₀ : dependentWordAugCell R L J xs (ys ∘ f) (V ∘ f) (A ∘ f)
        (indexedAugmentation (fun x => δ (f x))) (eqToHom e ≫ ε) =
      taggedRaggedRows (B ∘ g) Prod.mk (ys ∘ f) xs ≫ act 𝒮 Zₐ (fun x => p (f x)) xs ≫ eqToHom u.symm ≫ ε :=
    dependentWordAug_raw_rows R L J xs (ys ∘ f) (V ∘ f) (A ∘ f) (fun x => δ (f x)) (eqToHom e ≫ ε)
  have h₁ : dependentWordAugCell R L J (xs.map f) ys V A (indexedAugmentation δ) ε =
      taggedRaggedRows B Prod.mk ys (xs.map f) ≫ act 𝒮 Zₐ p (xs.map f) ≫ ε :=
    dependentWordAug_raw_rows R L J (xs.map f) ys V A δ ε
  have hs : taggedRaggedRows B Prod.mk ys (xs.map f) ≫ act 𝒮 Zₐ p (xs.map f) ≫ eqToHom u =
      eqToHom z ≫ taggedRaggedRows B (Prod.mk ∘ f) (ys ∘ f) xs ≫ act 𝒮 Zₐ (fun x => p (f x)) xs :=
    taggedRaggedRows_read_parents B V Prod.mk ys f xs p
  have j : taggedRaggedRows B Prod.mk ys (xs.map f) ≫ act 𝒮 Zₐ p (xs.map f) ≫ ε =
      eqToHom z ≫ taggedRaggedRows B (Prod.mk ∘ f) (ys ∘ f) xs ≫
        act 𝒮 Zₐ (fun x => p (f x)) xs ≫ eqToHom u.symm ≫ ε := by
    rw [← reassoc_of% hs, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have a := taggedRaggedRows_tag_heq B g Prod.mk (ys ∘ f) xs
  have w' : w.map g = xs.flatMap (M ∘ f) := by
    unfold w dependentWord
    simp only [List.map_flatMap, List.map_map]
    rfl
  let e₀ := (std_fold_map B g w).symm.trans (congrArg (fold 𝒮 Zₐ B) w')
  have v : HEq (taggedRaggedRows (B ∘ g) Prod.mk (ys ∘ f) xs ≫ act 𝒮 Zₐ (fun x => p (f x)) xs ≫
      eqToHom u.symm ≫ ε) (taggedRaggedRows B (Prod.mk ∘ f) (ys ∘ f) xs ≫ act 𝒮 Zₐ (fun x => p (f x)) xs ≫
      eqToHom u.symm ≫ ε) :=
    structural_seq_heq (K:=coeff (C:=C)) e₀ rfl (rfl : I = _) a HEq.rfl
  rw [h₀,h₁,j]
  exact v.trans (hom_source_pin_heq z _).symm

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
