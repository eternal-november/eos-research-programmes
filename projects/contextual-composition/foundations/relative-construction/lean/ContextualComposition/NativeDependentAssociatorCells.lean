module
public import ContextualComposition.NativeDependentAssociator
@[expose] public section

/-! Whole-cell ternary component laws. No map out of an empty sum is
replaced by a canonical map or decomposed into per-summand maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (P : TensorPrimitive T)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P)

include NL Q in
set_option backward.isDefEq.respectTransparency false in
theorem dependentAssoc_leaf_cell {Y : Type u} (a b d : C) (W : Y → C) (ys : List Y)
    (γ : fold 𝒮 Zₐ W ys ⟶ d) :
    (Lin.left L (T.obj a b)).collect W ys ≫ T.map (𝟙 (T.obj a b)) γ ≫ P.assoc a b d =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫
      (Lin.left L a).collect (fun y => T.obj b (W y)) ys ≫
      T.map (𝟙 a) ((Lin.left L b).collect W ys ≫ T.map (𝟙 b) γ) := by
  let F := leftFactor T a
  let H := leftFactor T (T.obj a b)
  let G := leftFactor T b
  let e := fold 𝒮 Zₐ W ys
  let q := (Lin.left L b).collect W ys
  let p := (Lin.left L a).collect (fun y => T.obj b (W y)) ys
  have f : H.map γ ≫ P.assoc a b d = P.assoc a b e ≫ F.map (G.map γ) := by
    have g := P.assoc_nat (𝟙 a) (𝟙 b) γ
    change T.map (T.map (𝟙 a) (𝟙 b)) γ ≫ P.assoc a b d = _ at g
    rw [T.map_id] at g
    exact g
  have g := (Q.al a b).collect W ys
  have o := Lin.collect_comp (Lin.left L b) (Lin.left L a) (NL.inner a) W ys
  change (Lin.left L (T.obj a b)).collect W ys ≫ P.assoc a b e =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫ ((Lin.left L b).comp (Lin.left L a)).collect W ys at g
  change (Lin.left L (T.obj a b)).collect W ys ≫ H.map γ ≫ P.assoc a b d =
    act 𝒮 Zₐ (fun y => P.assoc a b (W y)) ys ≫ p ≫ F.map (q ≫ G.map γ)
  rw [f, reassoc_of% g, o, F.map_comp]
  simp only [Category.assoc]
  rfl

include NR NL Q in
set_option backward.isDefEq.respectTransparency false in
theorem dependentAssoc_middle_cell {Y : Type u} (a b d : C) (B : Y → C) (ys : List Y)
    (δ : fold 𝒮 Zₐ B ys ⟶ b) :
    DependentFibre.gather R (fun y => T.obj a (B y)) d ys ≫
      T.map ((Lin.left L a).collect B ys ≫ T.map (𝟙 a) δ) (𝟙 d) ≫ P.assoc a b d =
    act 𝒮 Zₐ (fun y => P.assoc a (B y) d) ys ≫
      (Lin.left L a).collect (fun y => T.obj (B y) d) ys ≫
      T.map (𝟙 a) (DependentFibre.gather R B d ys ≫ T.map δ (𝟙 d)) := by
  let F := leftFactor T a
  let G := rightFactor (T:=T) d
  let M := fold 𝒮 Zₐ B ys
  let m := (Lin.left L a).collect B ys
  let b' := DependentFibre.gather R B d ys
  let p := DependentFibre.gather R (fun y => T.obj a (B y)) d ys
  let q := (Lin.left L a).collect (fun y => T.obj (B y) d) ys
  let u := act 𝒮 Zₐ (fun y => P.assoc a (B y) d) ys
  have h₀ : p ≫ G.map m ≫ P.assoc a M d = u ≫ q ≫ F.map b' := by
    have h := (Q.am a d).collect B ys
    rw [Lin.collect_comp _ _ (rightNatural R NR d), Lin.collect_comp _ _ (NL.inner a)] at h
    simp only [linRight_collect_gather] at h
    change (p ≫ G.map m) ≫ P.assoc a M d = u ≫ q ≫ F.map b' at h
    simpa only [Category.assoc] using h
  have h₁ : G.map (F.map δ) ≫ P.assoc a b d = P.assoc a M d ≫ F.map (G.map δ) :=
    P.assoc_nat (𝟙 a) δ (𝟙 d)
  change p ≫ G.map (m ≫ F.map δ) ≫ P.assoc a b d =
    u ≫ q ≫ F.map (b' ≫ G.map δ)
  rw [G.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [h₁, reassoc_of% h₀]

include NR Q in
set_option backward.isDefEq.respectTransparency false in
theorem dependentAssoc_parent_cell {X : Type u} (a b d : C) (A : X → C) (xs : List X)
    (α : fold 𝒮 Zₐ A xs ⟶ a) :
    DependentFibre.gather R (fun x => T.obj (A x) b) d xs ≫
      T.map (DependentFibre.gather R A b xs ≫ T.map α (𝟙 b)) (𝟙 d) ≫ P.assoc a b d =
    act 𝒮 Zₐ (fun x => P.assoc (A x) b d) xs ≫
      DependentFibre.gather R A (T.obj b d) xs ≫ T.map α (𝟙 (T.obj b d)) := by
  let G := rightFactor (T:=T) d
  let K := rightFactor (T:=T) b
  let M := fold 𝒮 Zₐ A xs
  let m := DependentFibre.gather R A b xs
  let p := DependentFibre.gather R (fun x => T.obj (A x) b) d xs
  let q := DependentFibre.gather R A (T.obj b d) xs
  let u := act 𝒮 Zₐ (fun x => P.assoc (A x) b d) xs
  have h₀ : p ≫ G.map m ≫ P.assoc M b d = u ≫ q := by
    have h := (Q.ar b d).collect A xs
    rw [Lin.collect_comp _ _ (rightNatural R NR d)] at h
    simp only [linRight_collect_gather] at h
    change (p ≫ G.map m) ≫ P.assoc M b d = u ≫ q at h
    simpa only [Category.assoc] using h
  have h₁ : G.map (K.map α) ≫ P.assoc a b d = P.assoc M b d ≫ T.map α (𝟙 (T.obj b d)) := by
    have h := P.assoc_nat α (𝟙 b) (𝟙 d)
    change _ = P.assoc M b d ≫ T.map α (T.map (𝟙 b) (𝟙 d)) at h
    rw [T.map_id] at h
    exact h
  change p ≫ G.map (m ≫ K.map α) ≫ P.assoc a b d = _
  rw [G.map_comp]
  simp only [Category.assoc]
  rw [h₁, reassoc_of% h₀]

include NR NL Q in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem dependentAssoc_middle_whole {Y W : Type u} (a b d : C) (B : Y → C) (D : Y → W → C)
    (ys : List Y) (ws : Y → List W)
    (δ : fold 𝒮 Zₐ B ys ⟶ b) (γ : ∀ y, fold 𝒮 Zₐ (D y) (ws y) ⟶ d)
    [(leftFactor T a).LaxBraided] (hl : SameLeftGather T a L) :
    let A₀ := fun k : Y × W => T.obj (T.obj a (B k.1)) (D k.1 k.2)
    let A₁ := dependentLabels (T:=T) B D
    let F := leftFactor T a
    let al := fun k : Y × W => P.assoc a (B k.1) (D k.1 k.2)
    let c := fun y => (Lin.left L (T.obj a (B y))).collect (D y) (ws y) ≫
      T.map (𝟙 (T.obj a (B y))) (γ y)
    let q := fun y => (Lin.left L (B y)).collect (D y) (ws y) ≫ T.map (𝟙 (B y)) (γ y)
    taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ c ys ≫
      DependentFibre.gather R (fun y => T.obj a (B y)) d ys ≫
      T.map ((Lin.left L a).collect B ys ≫ F.map δ) (𝟙 d) ≫ P.assoc a b d =
    act 𝒮 Zₐ al (dependentWord ys ws) ≫ (Lin.left L a).collect A₁ (dependentWord ys ws) ≫
      F.map (taggedRaggedRows A₁ Prod.mk ws ys ≫ act 𝒮 Zₐ q ys ≫
        DependentFibre.gather R B d ys ≫ T.map δ (𝟙 d)) := by
  intro A₀ A₁ F al c q
  let K := Lin.left L a
  let A₂ := fun k => F.obj (A₁ k)
  let B₀ := fun y => fold 𝒮 Zₐ (A₁ ∘ Prod.mk y) (ws y)
  let e := fun y => act 𝒮 Zₐ (fun w => al (y,w)) (ws y)
  let f := fun y => K.collect (A₁ ∘ Prod.mk y) (ws y)
  let s := fun y => P.assoc a (B y) d
  let r := fun y => T.obj (B y) d
  have h (y : Y) : c y ≫ s y = e y ≫ f y ≫ F.map (q y) :=
    (Category.assoc _ _ _).trans (dependentAssoc_leaf_cell R L P NL Q a (B y) d (D y) (ws y) (γ y))
  have g : act 𝒮 Zₐ c ys ≫ act 𝒮 Zₐ s ys =
      act 𝒮 Zₐ e ys ≫ act 𝒮 Zₐ f ys ≫ act 𝒮 Zₐ (fun y => F.map (q y)) ys := by
    have e₁ := act_seq 𝒮 Zₐ e (fun y => f y ≫ F.map (q y)) ys
    have e₂ := act_seq 𝒮 Zₐ f (fun y => F.map (q y)) ys
    exact (act_seq 𝒮 Zₐ c s ys).trans
      ((congrArg (fun v => act 𝒮 Zₐ v ys) (funext h)).trans
        (e₁.symm.trans (congrArg (fun v => act 𝒮 Zₐ e ys ≫ v) e₂.symm)))
  have n : act 𝒮 Zₐ (fun y => F.map (q y)) ys ≫ K.collect r ys =
      K.collect B₀ ys ≫ F.map (act 𝒮 Zₐ q ys) := Lin.collect_nat K (NL.inner a) q ys
  have hs : taggedRaggedRows A₂ Prod.mk ws ys ≫ act 𝒮 Zₐ f ys ≫ K.collect B₀ ys =
      K.collect A₁ (dependentWord ys ws) ≫ F.map (taggedRaggedRows A₁ Prod.mk ws ys) := by
    let F' := linearFunctor F
    have h₁ : (fun y => F'.collect (A₁ ∘ Prod.mk y) (ws y)) = f :=
      funext fun y => leftFactor_sameCollect T a L hl _ _
    have h₂ := leftFactor_sameCollect T a L hl B₀ ys
    have h₃ := leftFactor_sameCollect T a L hl A₁ (dependentWord ys ws)
    have z := collect_taggedRaggedRows F A₁ Prod.mk ws ys
    change taggedRaggedRows A₂ Prod.mk ws ys ≫ act 𝒮 Zₐ (fun y => F'.collect (A₁ ∘ Prod.mk y) (ws y)) ys ≫
        F'.collect B₀ ys = F'.collect A₁ (dependentWord ys ws) ≫ _ at z
    rw [h₁, h₂, h₃] at z
    exact z
  have hw : act 𝒮 Zₐ al (dependentWord ys ws) ≫ taggedRaggedRows A₂ Prod.mk ws ys =
      taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ e ys :=
    taggedRaggedRows_natural Prod.mk ws ys al
  rw [dependentAssoc_middle_cell R L P NR NL Q a b d B ys δ]
  change taggedRaggedRows A₀ Prod.mk ws ys ≫ act 𝒮 Zₐ c ys ≫ act 𝒮 Zₐ s ys ≫
    K.collect r ys ≫ F.map (DependentFibre.gather R B d ys ≫ T.map δ (𝟙 d)) = _
  rw [reassoc_of% g, ← reassoc_of% hw, reassoc_of% n, reassoc_of% hs]
  simp only [F.map_comp]
  rfl

section Whole
variable {X Y W : Type u}
variable (xs : List X) (ys : X → List Y) (ws : X → Y → List W)
variable (V : X → C) (B : X → Y → C) (D : X → Y → W → C)
variable {a b d : C}
variable (α : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ a)
variable (β : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ b)
variable (γ : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ d)

def dependentAssocLeftCell :
    fold 𝒮 Zₐ (assocLeftLabels T V B D) (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)) ⟶
      T.obj (T.obj a b) d :=
  let X₀ := dependentLabels (T:=T) V B
  let zs := dependentWord xs ys
  let cs := fun v : X × Y => (Lin.left L (X₀ v)).collect (D v.1 v.2) (ws v.1 v.2) ≫
    T.map (𝟙 (X₀ v)) (γ v.1 v.2)
  let bs := fun x => (Lin.left L (V x)).collect (B x) (ys x) ≫ T.map (𝟙 (V x)) (β x)
  let p := taggedRaggedRows X₀ Prod.mk ys xs ≫ act 𝒮 Zₐ bs xs ≫
    DependentFibre.gather R V b xs ≫ T.map α (𝟙 b)
  taggedRaggedRows (assocLeftLabels T V B D) Prod.mk (fun t => ws t.1 t.2) zs ≫
    act 𝒮 Zₐ cs zs ≫ DependentFibre.gather R X₀ d zs ≫ T.map p (𝟙 d)

def dependentAssocRightCell :
    fold 𝒮 Zₐ (assocRightLabels T V B D) (dependentWord xs (fun x => dependentWord (ys x) (ws x))) ⟶
      T.obj a (T.obj b d) :=
  let D₀ (x : X) := dependentLabels (T:=T) (B x) (D x)
  let ls (x : X) := dependentWord (ys x) (ws x)
  let p (x : X) := taggedRaggedRows (D₀ x) Prod.mk (ws x) (ys x) ≫
    act 𝒮 Zₐ (fun y => (Lin.left L (B x y)).collect (D x y) (ws x y) ≫ T.map (𝟙 (B x y)) (γ x y)) (ys x) ≫
    DependentFibre.gather R (B x) d (ys x) ≫ T.map (β x) (𝟙 d)
  taggedRaggedRows (assocRightLabels T V B D) Prod.mk ls xs ≫
    act 𝒮 Zₐ (fun x => (Lin.left L (V x)).collect (D₀ x) (ls x) ≫ T.map (𝟙 (V x)) (p x)) xs ≫
      DependentFibre.gather R V (T.obj b d) xs ≫ T.map α (𝟙 (T.obj b d))

include NR NL Q in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
/-- Both original ternary whole-cell schedules on the same chosen fibre,
identified by the literal addressed associator. Every coefficient argument
is an actual whole-fibre arrow; zero rows are part of the statement. -/
theorem dependentAssoc_whole
    [lF : ∀ a : C, (leftFactor T a).LaxBraided]
    [(rightFactor (T:=T) d).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : SameRightGather R d) :
    let A₀ := assocLeftLabels T V B D
    let A₀' := A₀ ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
    let w₀ := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
    let w₁ := dependentWord xs (fun x => dependentWord (ys x) (ws x))
    let p := fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2)
    let pin : fold 𝒮 Zₐ A₀ w₀ = fold 𝒮 Zₐ A₀' w₁ :=
      (std_fold_map A₀' tripleRetag w₀).symm.trans (congrArg (fold 𝒮 Zₐ A₀') (tripleRetag_word xs ys ws))
    dependentAssocLeftCell R L xs ys ws V B D α β γ ≫ P.assoc a b d =
      eqToHom pin ≫ act 𝒮 Zₐ p w₁ ≫ dependentAssocRightCell R L xs ys ws V B D α β γ := by
  intro A₀ A₀' w₀ w₁ p pin
  let A₁ := assocRightLabels T V B D
  let X₀ := dependentLabels (T:=T) V B
  let zs := dependentWord xs ys
  let C₀ := fun x => dependentWord (ys x) (ws x)
  let lt := fun (x : X) (v : Y × W) => ((x,v.1),v.2)
  let rt := fun (x : X) (v : Y × W) => (x,v)
  let G := rightFactor (T:=T) d
  let K := Lin.right R d
  let H := fun x => T.obj (V x) b
  let XX := fun t => G.obj (X₀ t)
  let L₀ := fun (v : X × Y) =>
    (Lin.left L (X₀ v)).collect (D v.1 v.2) (ws v.1 v.2) ≫ T.map (𝟙 (X₀ v)) (γ v.1 v.2)
  let s := fun x => (Lin.left L (V x)).collect (B x) (ys x) ≫ T.map (𝟙 (V x)) (β x)
  let sh := fun x => K.collect (X₀ ∘ Prod.mk x) (ys x)
  let a₀ := fun x => sh x ≫ G.map (s x)
  let n := fun x => P.assoc (V x) b d
  let g₁ := DependentFibre.gather R V b xs ≫ T.map α (𝟙 b)
  let g₂ := DependentFibre.gather R V (T.obj b d) xs ≫ T.map α (𝟙 (T.obj b d))
  let D₀ (x : X) := dependentLabels (T:=T) (B x) (D x)
  let pr (x : X) := taggedRaggedRows (D₀ x) Prod.mk (ws x) (ys x) ≫
    act 𝒮 Zₐ (fun y => (Lin.left L (B x y)).collect (D x y) (ws x y) ≫ T.map (𝟙 (B x y)) (γ x y)) (ys x) ≫
    DependentFibre.gather R (B x) d (ys x) ≫ T.map (β x) (𝟙 d)
  let a' := fun x => (Lin.left L (V x)).collect (D₀ x) (C₀ x) ≫ T.map (𝟙 (V x)) (pr x)
  have hg : DependentFibre.gather R X₀ d zs ≫ G.map (taggedRaggedRows X₀ Prod.mk ys xs) =
      taggedRaggedRows XX Prod.mk ys xs ≫ act 𝒮 Zₐ sh xs ≫ K.collect (fun x => fold 𝒮 Zₐ (X₀ ∘ Prod.mk x) (ys x)) xs := by
    let G' := linearFunctor G
    have eqn {Z : Type u} (A : Z → C) (zs : List Z) : G'.collect A zs = K.collect A zs :=
      (rightFactor_sameCollect R hr A zs).trans (linRight_collect_gather R d A zs).symm
    have r₀ : (fun x => G'.collect (X₀ ∘ Prod.mk x) (ys x)) = sh := funext fun x => eqn _ _
    have r₁ := eqn (fun x => fold 𝒮 Zₐ (X₀ ∘ Prod.mk x) (ys x)) xs
    have r₂ := eqn X₀ zs
    have z := collect_taggedRaggedRows G X₀ Prod.mk ys xs
    change taggedRaggedRows XX Prod.mk ys xs ≫ act 𝒮 Zₐ (fun x => G'.collect (X₀ ∘ Prod.mk x) (ys x)) xs ≫
      G'.collect (fun x => fold 𝒮 Zₐ (X₀ ∘ Prod.mk x) (ys x)) xs =
      G'.collect X₀ zs ≫ G.map (taggedRaggedRows X₀ Prod.mk ys xs) at z
    rw [r₀, r₁, r₂] at z
    simp only [K, linRight_collect_gather] at z ⊢
    exact z.symm
  have hn : K.collect (fun x => fold 𝒮 Zₐ (X₀ ∘ Prod.mk x) (ys x)) xs ≫ G.map (act 𝒮 Zₐ s xs) =
      act 𝒮 Zₐ (fun x => G.map (s x)) xs ≫ K.collect H xs :=
    (Lin.collect_nat K (rightNatural R NR d) s xs).symm
  have hp : K.collect H xs ≫ G.map g₁ ≫ P.assoc a b d = act 𝒮 Zₐ n xs ≫ g₂ := by
    rw [linRight_collect_gather]
    exact dependentAssoc_parent_cell R L P NR Q a b d V xs α
  have hc : act 𝒮 Zₐ sh xs ≫ act 𝒮 Zₐ (fun x => G.map (s x)) xs = act 𝒮 Zₐ a₀ xs :=
    act_seq 𝒮 Zₐ sh (fun x => G.map (s x)) xs
  let t := fun x => taggedRaggedRows (A₀ ∘ lt x) Prod.mk (ws x) (ys x) ≫
     act 𝒮 Zₐ (fun y => L₀ (x,y)) (ys x)
  let z := fun x => act 𝒮 Zₐ (fun y => p (rt x y)) (C₀ x)
  have h₂ (x : X) : t x ≫ a₀ x ≫ n x = z x ≫ a' x := by
    let u := dependentAssoc_middle_whole R L P NR NL Q (V x) b d
      (B x) (D x) (ys x) (ws x) (β x) (γ x) (hl (V x))
    unfold a₀ t sh
    rw [linRight_collect_gather]
    simp only [Category.assoc]
    exact u
  have hh : act 𝒮 Zₐ t xs ≫ act 𝒮 Zₐ a₀ xs ≫ act 𝒮 Zₐ n xs = act 𝒮 Zₐ z xs ≫ act 𝒮 Zₐ a' xs :=
    (congrArg (fun f => act 𝒮 Zₐ t xs ≫ f) (act_seq 𝒮 Zₐ a₀ n xs)).trans
      ((act_seq 𝒮 Zₐ t (fun x => a₀ x ≫ n x) xs).trans
        ((congrArg (fun f => act 𝒮 Zₐ f xs) (funext h₂)).trans (act_seq 𝒮 Zₐ z a' xs).symm))
  let fp := congrArg (fold 𝒮 Zₐ A₀) (tripleWord_flat xs ys ws)
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let pp := taggedRaggedRows A₀ lt C₀ xs
  let qq := taggedRaggedRows A₀' rt C₀ xs
  have qqpin : fold 𝒮 Zₐ A₀' w₁ = fold 𝒮 Zₐ A₀ (xs.flatMap (fun x => (C₀ x).map (lt x))) := pin.symm.trans fp
  have ht : qq = eqToHom qqpin ≫ pp := by
    have k := taggedRaggedRows_tag_heq A₀ g.symm rt C₀ xs
    have q := heq_paste qqpin (rfl : _ = _) k
    rw [eqToHom_refl, Category.comp_id] at q
    exact q
  have ho : eqToHom pin ≫ qq = eqToHom fp ≫ pp := by rw [ht, eqToHom_trans_assoc]
  have zz : act 𝒮 Zₐ p w₁ ≫ taggedRaggedRows A₁ rt C₀ xs = qq ≫ act 𝒮 Zₐ z xs :=
    taggedRaggedRows_natural rt C₀ xs p
  change (taggedRaggedRows A₀ Prod.mk (fun t => ws t.1 t.2) zs ≫ act 𝒮 Zₐ L₀ zs ≫
    DependentFibre.gather R X₀ d zs ≫ G.map (taggedRaggedRows X₀ Prod.mk ys xs ≫ act 𝒮 Zₐ s xs ≫ g₁)) ≫
      P.assoc a b d = eqToHom pin ≫ act 𝒮 Zₐ p w₁ ≫
        taggedRaggedRows A₁ rt C₀ xs ≫ act 𝒮 Zₐ a' xs ≫ g₂
  simp only [Category.assoc, G.map_comp]
  rw [reassoc_of% hg, reassoc_of% hn, hp, reassoc_of% hc]
  rw [reassoc_of% nestedDependentRows, reassoc_of% hh, reassoc_of% zz, reassoc_of% ho]

end Whole

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
