module
public import ContextualComposition.NativeOrderedMapComposition
@[expose] public section

/-! The non-disjoint exchange in dependent composition at one intermediate
parent: its second continuation cell is constant across precisely the
source parents merged by its first parent cell. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w z
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable (M : AddCross S Z) (R : Gather S T Z) (L : LeftGather S T Z)
variable (N : GridBinary M R L) (NL : GatherLeftNat L)
variable {X : Type w} {Y : Type z} (V : X → C) (W : Y → C) (A : X → Y → C)
variable (xs : List X) (ys : List Y)
variable (p : ∀ x y, K.Hom (A x y) (T.obj (V x) (W y)))
variable {a b : C} (α : K.Hom (fold S Z V xs) a)
variable (β : K.Hom (fold S Z W ys) b)

/-- After the first child cells, apply the second continuation whole
aggregate at every parent in the chosen first parent fibre, then merge
that fibre using the opaque first parent cell. -/
def continuationBeforeFirstParent :=
  K.seq (act S Z (fun x =>
    K.seq (act S Z (p x) ys)
      (K.seq (Lin.collect (Lin.left L (V x)) W ys) (T.map (K.id (V x)) β))) xs)
    (K.seq (gather R V b xs) (T.map α (K.id b)))

theorem parentMajor_then_continuation :
    K.seq (parentMajorChildGather R L V W A xs ys p α) (T.map (K.id a) β) =
      continuationBeforeFirstParent R L V W A xs ys p α β := by
  let z := fold S Z W ys
  let k := fun x => K.seq (act S Z (p x) ys) (Lin.collect (Lin.left L (V x)) W ys)
  let q := fun x => T.map (K.id (V x)) β
  let f := fold S Z V xs
  have m : K.seq (T.map α (K.id z)) (T.map (K.id a) β) =
      K.seq (T.map (K.id f) β) (T.map α (K.id b)) := by
    rw [← T.map_seq, ← T.map_seq, K.id_seq, K.seq_id, K.id_seq, K.seq_id]
  unfold parentMajorChildGather continuationBeforeFirstParent
  simp only [K.assoc]
  rw [m, ← K.assoc (gather R V z xs), gather_nat, K.assoc]
  change K.seq (act S Z k xs) (K.seq (act S Z q xs) _) = _
  simp only [← K.assoc]
  rw [act_seq]

include N NL in
theorem childMajor_then_continuation :
    K.seq (transposeBlock M A ys xs)
      (K.seq (childMajorParentGather R L V W A xs ys p α) (T.map (K.id a) β)) =
      continuationBeforeFirstParent R L V W A xs ys p α β := by
  rw [← K.assoc, child_parent_regrouping M R L N NL, parentMajor_then_continuation]


section AllGroups
variable (NR : GatherOuterNat R)
variable {I : Type*} (is : List I) (xs : I → List X) (ys : I → List Y)
variable (v₀ : X → C) (v₁ : I → C) (w₁ : I → Y → C)
variable (a₀ : I → X → Y → C)
variable (p : ∀ i x y, K.Hom (a₀ i x y) (T.obj (v₀ x) (w₁ i y)))
variable {a b : C}
variable (f : ∀ i, K.Hom (fold S Z v₀ (xs i)) (v₁ i))
variable (g : ∀ i, K.Hom (fold S Z (w₁ i) (ys i)) b)
variable (h : K.Hom (fold S Z v₁ is) a)

include NR in
/-- After the inner two-variable interchange, only first parent maps
remain between the two outer gathers. They commute through the second
outer gather by its ordinary naturality. All rows remain present. -/
theorem parentGroups_then_merge :
    let one := fun i => parentMajorChildGather R L v₀ (w₁ i) (a₀ i) (xs i) (ys i) (p i) (f i)
    let two := fun i => T.map (K.id (v₁ i)) (g i)
    let step := fun i => K.seq (act S Z (fun x =>
      K.seq (act S Z (p i x) (ys i))
        (K.seq (Lin.collect (Lin.left L (v₀ x)) (w₁ i) (ys i)) (T.map (K.id (v₀ x)) (g i)))) (xs i))
      (gather R v₀ b (xs i))
    K.seq (act S Z one is) (K.seq (act S Z two is)
      (K.seq (gather R v₁ b is) (T.map h (K.id b)))) =
    K.seq (act S Z step is) (K.seq (gather R (fun i => fold S Z v₀ (xs i)) b is)
      (T.map (K.seq (act S Z f is) h) (K.id b))) := by
  intro one two step
  let q := fun i => T.map (f i) (K.id b)
  have ex : (fun i => K.seq (one i) (two i)) = (fun i => K.seq (step i) (q i)) := by
    funext i
    have z := parentMajor_then_continuation R L v₀ (w₁ i) (a₀ i) (xs i) (ys i)
      (p i) (f i) (g i)
    unfold continuationBeforeFirstParent at z
    unfold one two step q
    exact z.trans (K.assoc _ _ _).symm
  rw [← K.assoc, act_seq, ex, ← act_seq]
  simp only [K.assoc]
  rw [← K.assoc (act S Z q is), gather_outer NR]
  simp only [K.assoc]
  rw [← T.map_seq, K.id_seq]

end AllGroups
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v i
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "MC" => symmetricCross (C:=C)

set_option backward.isDefEq.respectTransparency false in
/-- The non-disjoint exchange with both specified raw flat chart arrows,
not just their nested additive-object counterparts. -/
theorem flat_child_then_second_continuation {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (N : GridBinary MC R L) (NL : GatherLeftNat L)
    {Q X Y : Type u} (A : Q → C) (P : X → Y → GridExpr Q) (xs : List X) (ys : List Y)
    (V : X → C) (W : Y → C)
    (p : ∀ x y, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x y) ⟶ T.obj (V x) (W y))
    {a b : C} (α : fold 𝒮 Zₐ V xs ⟶ a) (β : fold 𝒮 Zₐ W ys ⟶ b) :
    let F := fun x y => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P x y)
    let row := GridExpr.over (fun x => GridExpr.over (P x) ys) xs
    let col := GridExpr.over (fun y => GridExpr.over (fun x => P x y) xs) ys
    let order := gridOrder (GridCircuit.transpose P ys xs)
    AddressOrder.mapSum additiveStructure A order ≫
      compressGrid A col ≫ eqToHom (colMatrix_pin A P xs ys) ≫
        childMajorParentGather R L V W F xs ys p α ≫ T.map (𝟙 a) β =
    compressGrid A row ≫ eqToHom (rowMatrix_pin A P xs ys) ≫
      continuationBeforeFirstParent R L V W F xs ys p α β := by
  intro F row col order
  have h := flat_child_parent_regrouping A P xs ys R L N NL V W p α
  let g : T.obj a (fold 𝒮 Zₐ W ys) ⟶ T.obj a b := T.map (𝟙 a) β
  have e := congrArg (fun k => k ≫ g) h
  simp only [Category.assoc] at e
  refine e.trans ?_
  exact congrArg (fun k => compressGrid A row ≫ eqToHom (rowMatrix_pin A P xs ys) ≫ k)
    (parentMajor_then_continuation R L V W F xs ys p α β)


set_option backward.isDefEq.respectTransparency false in
/-- Graft the actual first-stage coefficient charts into the second-stage
chart, then run the opaque first-stage cells. The result is exactly the
raw native composite partition followed by the second-stage coefficient
interpretation. No distribution is chosen by comparing resource labels. -/
theorem compressGrid_grafted_cells {Q : Type u} {I : Type i}
    (A : Q → C) (B : I → C) (P : I → GridExpr Q) (e : GridExpr I)
    (p : ∀ i, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i) ⟶ B i) :
    let L := fun i => (P i).leaves
    let _H := fun i => GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P i)
    let c := fun i => compressGrid A (P i) ≫ p i
    eqToHom (congrArg (fold 𝒮 Zₐ A) (graftGrid_leaves P e).symm) ≫
      compressGrid A (graftGrid P e) ≫ eqToHom (graftGrid_eval A P e) ≫
      GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e =
    rowsChart A L e.leaves ≫ act 𝒮 Zₐ c e.leaves ≫ compressGrid B e := by
  intro L H c
  let F := fold 𝒮 Zₐ A
  let d := congrArg F (graftGrid_leaves P e)
  let h := graftGrid_eval A P e
  let r := rowsChart A L e.leaves
  let u := fun i => compressGrid A (P i)
  have q : compressGrid A (graftGrid P e) ≫ eqToHom h =
      eqToHom d ≫ r ≫ act 𝒮 Zₐ u e.leaves ≫ compressGrid H e := compressGrid_graft A P e
  have k := compressGrid_natural (A:=H) (B:=B) p e
  change eqToHom d.symm ≫ compressGrid A (graftGrid P e) ≫ eqToHom h ≫
      GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e = _
  rw [reassoc_of% q, ← k]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have v : act 𝒮 Zₐ u e.leaves ≫ act 𝒮 Zₐ p e.leaves = act 𝒮 Zₐ c e.leaves :=
    act_seq (S:=𝒮) (Z:=Zₐ) u p _
  rw [reassoc_of% v]


local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Exact sequential native cell normal form. Once the intermediate
chart and the local first-cell charts are pinned to their actual fibres,
grafting those charts computes the coefficient of the original native
composite. The theorem does not assume or identify a second route. -/
theorem readCompositeWordCell_grafted
    {X Y D : Type u} [DecidableEq Y] [DecidableEq D]
    {xs : List X} {ys : List Y} {zs : List D}
    (A : X → C) (B : Y → C) (D' : D → C) (f : X → Y) (g : Y → D)
    (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hx : xs.Nodup) (hy : ys.Nodup) (hz : zs.Nodup)
    (k : Fin zs.length)
    (P : Fin ys.length → GridExpr X) (e : GridExpr (Fin ys.length))
    (d : e.leaves = fibreList (wordCarrier g hg hz) k)
    (hP : ∀ j : Fin ys.length, (P j).leaves = wordFibre xs f ys[j])
    (p : ∀ j : Fin ys.length, GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (P j) ⟶ B ys[j])
    (q : ∀ j : Fin zs.length, fold 𝒮 Zₐ B (wordFibre ys g zs[j]) ⟶ D' zs[j])
    (r : AddressOrder X (wordFibre xs (g ∘ f) zs[k]) (graftGrid P e).leaves)
    (q' : GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun i : Fin ys.length => B ys[i]) e ⟶ D' zs[k])
    (hq : compressGrid (fun i : Fin ys.length => B ys[i]) e ≫ q' =
      eqToHom (congrArg (fold 𝒮 Zₐ (fun i : Fin ys.length => B ys[i])) d) ≫
        eqToHom (wordCarrier_fibre_pin g hg hz B k) ≫ q k) :
    let p₀ := fun i => eqToHom (congrArg (fold 𝒮 Zₐ A) (hP i).symm) ≫ compressGrid A (P i) ≫ p i
    readNativeWordCell A D' (g ∘ f) (fun x hx => hg _ (hf x hx)) hz
      ((wordNativeMap f hf hy A B p₀).comp (wordNativeMap g hg hz B D' q))
      (wordCarrier_comp f g hf hg hy hz).symm k =
    AddressOrder.mapSum additiveStructure A r ≫ compressGrid A (graftGrid P e) ≫
      eqToHom (graftGrid_eval A P e) ≫ GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e ≫ q' := by
  intro p₀
  let F := fold 𝒮 Zₐ A
  let B₀ := fun i : Fin ys.length => B ys[i]
  let L := fun i => (P i).leaves
  let M := fun i : Fin ys.length => wordFibre xs f ys[i]
  let c := fun i => compressGrid A (P i) ≫ p i
  let e₁ := graftGrid_leaves P e
  let e₂ : e.leaves.flatMap L = e.leaves.flatMap M := congrArg (fun K => e.leaves.flatMap K) (funext hP)
  let e₃ := congrArg (fun v => v.flatMap M) d
  let t := e₁.trans (e₂.trans e₃)
  let r₀ := r.seq (castOrder t)
  have a : AddressOrder.mapSum additiveStructure A r₀ =
      AddressOrder.mapSum additiveStructure A r ≫ eqToHom (congrArg F t) := by
    unfold r₀
    change AddressOrder.mapSum additiveStructure A r ≫ AddressOrder.mapSum additiveStructure A (castOrder t) = _
    rw [castOrder_map]
  have k0 := readCompositeWordCell_raw A B D' f g hf hg hy hz hx p₀ q k r₀
  rw [k0, a]
  simp only [Category.assoc]
  have k1 :
      rowsChart A L e.leaves ≫ act 𝒮 Zₐ c e.leaves =
      eqToHom (congrArg F e₂) ≫ rowsChart A M e.leaves ≫ act 𝒮 Zₐ p₀ e.leaves := by
    let eₓ := fun i => eqToHom (congrArg F (hP i))
    have x := rowsChart_rows_congr A hP e.leaves
    have y := act_seq (S:=𝒮) (Z:=Zₐ) eₓ p₀ e.leaves
    have z : (fun i => eₓ i ≫ p₀ i) = c := by
      funext i
      unfold eₓ p₀ c
      rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change act 𝒮 Zₐ eₓ e.leaves ≫ act 𝒮 Zₐ p₀ e.leaves = _ at y
    rw [z] at y
    rw [← y, ← Category.assoc, x, Category.assoc]
  have k2 :
      eqToHom (congrArg F e₃) ≫ rowsChart A M (fibreList (wordCarrier g hg hz) k) ≫
        act 𝒮 Zₐ p₀ (fibreList (wordCarrier g hg hz) k) =
      rowsChart A M e.leaves ≫ act 𝒮 Zₐ p₀ e.leaves ≫ eqToHom (congrArg (fold 𝒮 Zₐ B₀) d) := by
    have Z {s t : List (Fin ys.length)} (h : s = t) :
        eqToHom (congrArg F (congrArg (fun v => v.flatMap M) h)) ≫ rowsChart A M t ≫ act 𝒮 Zₐ p₀ t =
          rowsChart A M s ≫ act 𝒮 Zₐ p₀ s ≫ eqToHom (congrArg (fold 𝒮 Zₐ B₀) h) := by
      cases h
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact Z d
  have hpart := compressGrid_grafted_cells A B₀ P e p
  dsimp only at hpart
  have hpart' :
      compressGrid A (graftGrid P e) ≫ eqToHom (graftGrid_eval A P e) ≫ GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e =
      eqToHom (congrArg F e₁) ≫ rowsChart A L e.leaves ≫ act 𝒮 Zₐ c e.leaves ≫ compressGrid B₀ e := by
    have H := congrArg (fun h => eqToHom (congrArg F e₁) ≫ h) hpart
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at H
    exact H
  rw [reassoc_of% hpart', hq, reassoc_of% k1, ← reassoc_of% k2]
  rw [reassoc_of% eqToHom_trans (congrArg F e₁) (congrArg F e₂),
    reassoc_of% eqToHom_trans ((congrArg F e₁).trans (congrArg F e₂)) (congrArg F e₃)]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
