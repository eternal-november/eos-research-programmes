module
public import ContextualComposition.NativeFubiniTreeStructuralPath
@[expose] public section

/-! Normalize literal symmetric monoidal tensor paths on distinct
occurrence tags, separating atom labels from the empty tensor unit.
The monoidal structure here may be instantiated by multiplication. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X : Type w} (A : X → C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "F" => fold 𝒮 Zₐ A
local notation "R" => AddressOrder.mapSum additiveStructure A
local notation "J" => join additiveStructure A

def blockSwapOrder (xs ys : List X) : AddressOrder X (xs ++ ys) (ys ++ xs) :=
  (castOrder (congrArg (xs ++ ·) (List.append_nil ys).symm)).seq
    ((taggedBlockSwap xs ys []).seq (castOrder (congrArg (ys ++ ·) (List.append_nil xs))))

set_option backward.isDefEq.respectTransparency false in
theorem packBlocks_empty (xs ys : List X) :
    eqToHom (congrArg F (congrArg (xs ++ ·) (List.append_nil ys).symm)) ≫
      packBlocks A xs ys [] ≫ (ρ_ (F xs ⊗ F ys)).hom = J xs ys := by
  let q := J xs ys
  let x := J (xs ++ ys) []
  let l := (List.append_nil (xs ++ ys)).symm
  let a := List.append_assoc xs ys ([] : List X)
  let e := congrArg (xs ++ ·) (List.append_nil ys).symm
  have z : J xs (ys ++ []) ≫ (F xs ◁ J ys []) =
      eqToHom (congrArg F a.symm) ≫ x ≫ q ▷ Zₐ ≫ (α_ (F xs) (F ys) Zₐ).hom := by
    have h := std_join_assoc A xs ys []
    change eqToHom (congrArg F a) ≫ _ = x ≫ q ▷ Zₐ ≫ (α_ (F xs) (F ys) Zₐ).hom at h
    apply (cancel_epi (eqToHom (congrArg F a))).mp
    rw [h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have ee : eqToHom (congrArg F e) ≫ eqToHom (congrArg F a.symm) = eqToHom (congrArg F l) := by
    rw [eqToHom_trans]
  have nn : (q ▷ Zₐ) ≫ (ρ_ (F xs ⊗ F ys)).hom =
      (ρ_ (F (xs ++ ys))).hom ≫ q := rightUnitor_naturality q
  unfold packBlocks
  change eqToHom (congrArg F e) ≫
    (J xs (ys ++ []) ≫ (F xs ◁ J ys []) ≫ (α_ (F xs) (F ys) Zₐ).inv) ≫
      (ρ_ (F xs ⊗ F ys)).hom = q
  simp only [Category.assoc, reassoc_of% z]
  simp only [Iso.hom_inv_id_assoc, reassoc_of% ee]
  unfold x
  rw [← Category.assoc (eqToHom (congrArg F l)), std_join_right_unit]
  exact (congrArg (fun k => (ρ_ (F (xs ++ ys))).inv ≫ k) nn).trans (Iso.inv_hom_id_assoc _ _)

set_option backward.isDefEq.respectTransparency false in
theorem std_join_block_swap (xs ys : List X) :
    R (blockSwapOrder xs ys) ≫ J ys xs =
      J xs ys ≫ (β_ (F xs) (F ys)).hom := by
  let e := congrArg (xs ++ ·) (List.append_nil ys).symm
  let f := congrArg (ys ++ ·) (List.append_nil xs).symm
  let p := taggedBlockSwap xs ys []
  let P := packBlocks A xs ys []
  let Q := packBlocks A ys xs []
  let x := F xs
  let y := F ys
  have h₀ := packBlocks_empty A xs ys
  have h₁ := packBlocks_empty A ys xs
  have h₂ := swap_pack_blocks A xs ys []
  have h₃ : (β_ x y).hom ▷ Zₐ ≫ (ρ_ (y ⊗ x)).hom = (ρ_ (x ⊗ y)).hom ≫ (β_ x y).hom :=
    rightUnitor_naturality (β_ x y).hom
  have cancel : eqToHom (congrArg F f.symm) ≫ eqToHom (congrArg F f) = 𝟙 _ := by
    rw [eqToHom_trans]
    rfl
  change R ((castOrder e).seq (p.seq (castOrder f.symm))) ≫ J ys xs = J xs ys ≫ (β_ x y).hom
  rw [← h₁, ← h₀]
  simp only [AddressOrder.mapSum, Category.assoc, castOrder_map, reassoc_of% cancel]
  change eqToHom (congrArg F e) ≫ R p ≫ Q ≫ (ρ_ (y ⊗ x)).hom =
    eqToHom (congrArg F e) ≫ P ≫ (ρ_ (x ⊗ y)).hom ≫ (β_ x y).hom
  rw [reassoc_of% h₂]
  exact congrArg (fun g => eqToHom (congrArg F e) ≫ P ≫ g) h₃

set_option backward.isDefEq.respectTransparency false in
theorem SumTree.chart_block_swap (t s : SumTree X) :
    SumTree.chart A (.plus t s) ≫ (β_ (SumTree.eval A t) (SumTree.eval A s)).hom =
      R (blockSwapOrder t.leaves s.leaves) ≫ SumTree.chart A (.plus s t) := by
  let p := SumTree.chart A t
  let q := SumTree.chart A s
  change (J t.leaves s.leaves ≫ (p ⊗ₘ q)) ≫ _ =
      R (blockSwapOrder t.leaves s.leaves) ≫ (J s.leaves t.leaves ≫ (q ⊗ₘ p))
  rw [Category.assoc, braiding_naturality, ← Category.assoc (J t.leaves s.leaves), ← std_join_block_swap,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem SumTree.chart_right_unit (t : SumTree X) :
    SumTree.chart A (.plus t .zero) ≫ (ρ_ (SumTree.eval A t)).hom =
      eqToHom (congrArg F (List.append_nil t.leaves)) ≫ SumTree.chart A t := by
  let p := SumTree.chart A t
  let f := congrArg F (List.append_nil t.leaves)
  apply (cancel_epi (eqToHom f.symm)).mp
  have nu : (p ▷ Zₐ) ≫ (ρ_ (SumTree.eval A t)).hom = (ρ_ (F t.leaves)).hom ≫ p := rightUnitor_naturality p
  let j : F (t.leaves ++ []) ⟶ F t.leaves ⊗ Zₐ := J t.leaves []
  have cj : eqToHom f.symm ≫ j = (ρ_ (F t.leaves)).inv := std_join_right_unit A t.leaves
  change eqToHom f.symm ≫ (j ≫ (p ⊗ₘ 𝟙 Zₐ)) ≫ (ρ_ (SumTree.eval A t)).hom =
    eqToHom f.symm ≫ eqToHom f ≫ p
  rw [tensorHom_id]
  simp only [Category.assoc, reassoc_of% cj, nu, Iso.inv_hom_id_assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

/-- The formal structural tensor circuits are independent of coefficient
objects. Nullary vertices contain no resource-occurrence tag. -/
inductive TensorCircuit (X : Type w) : SumTree X → SumTree X → Type w where
  | ident (t : SumTree X) : TensorCircuit X t t
  | assoc (t s q : SumTree X) : TensorCircuit X (.plus (.plus t s) q) (.plus t (.plus s q))
  | swap (t s : SumTree X) : TensorCircuit X (.plus t s) (.plus s t)
  | runit (t : SumTree X) : TensorCircuit X (.plus t .zero) t
  | tensor {a b c d : SumTree X} : TensorCircuit X a b → TensorCircuit X c d → TensorCircuit X (.plus a c) (.plus b d)
  | seq {a b c : SumTree X} : TensorCircuit X a b → TensorCircuit X b c → TensorCircuit X a c
  | reverse {a b : SumTree X} : TensorCircuit X a b → TensorCircuit X b a

namespace TensorCircuit

noncomputable def order : {a b : SumTree X} → TensorCircuit X a b → AddressOrder X a.leaves b.leaves
  | _, _, .ident t => .ident t.leaves
  | _, _, .assoc t s q => castOrder (List.append_assoc t.leaves s.leaves q.leaves)
  | _, _, .swap t s => blockSwapOrder t.leaves s.leaves
  | _, _, .runit t => castOrder (List.append_nil t.leaves)
  | _, _, .tensor p q => (order p).parallel (order q)
  | _, _, .seq p q => .seq (order p) (order q)
  | _, _, .reverse p => Classical.choice (AddressOrder.ofPerm (order p).perm.symm)

def evaluate : {a b : SumTree X} → TensorCircuit X a b → (SumTree.eval (C:=C) A a ≅ SumTree.eval (C:=C) A b)
  | _, _, .ident _ => Iso.refl _
  | _, _, .assoc t s q => α_ (SumTree.eval A t) (SumTree.eval A s) (SumTree.eval A q)
  | _, _, .swap t s => β_ (SumTree.eval A t) (SumTree.eval A s)
  | _, _, .runit t => ρ_ (SumTree.eval A t)
  | _, _, .tensor p q => (evaluate p) ⊗ᵢ (evaluate q)
  | _, _, .seq p q => (evaluate p).trans (evaluate q)
  | _, _, .reverse p => (evaluate p).symm

set_option backward.isDefEq.respectTransparency false in
theorem normalize {a b : SumTree X} (p : TensorCircuit X a b) (hn : a.leaves.Nodup) :
    (p.evaluate A).hom = SumTree.changeChart A p.order := by
  induction p with
  | ident t => exact (SumTree.changeChart_id A t).symm
  | assoc t s q =>
    apply (SumTree.chartInv A (.plus (.plus t s) q)).cancelL
    change SumTree.chart A (.plus (.plus t s) q) ≫ _ = SumTree.chart A (.plus (.plus t s) q) ≫ _
    rw [SumTree.chart_changeChart]
    change SumTree.chart A (.plus (.plus t s) q) ≫ (α_ (SumTree.eval A t) (SumTree.eval A s) (SumTree.eval A q)).hom =
      R (castOrder (List.append_assoc t.leaves s.leaves q.leaves)) ≫ SumTree.chart A (.plus t (.plus s q))
    rw [castOrder_map]
    exact SumTree.chart_assoc A t s q
  | swap t s =>
    apply (SumTree.chartInv A (.plus t s)).cancelL
    change SumTree.chart A (.plus t s) ≫ _ = SumTree.chart A (.plus t s) ≫ _
    rw [SumTree.chart_changeChart]
    exact SumTree.chart_block_swap A t s
  | runit t =>
    apply (SumTree.chartInv A (.plus t .zero)).cancelL
    change SumTree.chart A (.plus t .zero) ≫ _ = SumTree.chart A (.plus t .zero) ≫ _
    rw [SumTree.chart_changeChart]
    change SumTree.chart A (.plus t .zero) ≫ (ρ_ (SumTree.eval A t)).hom =
      R (castOrder (List.append_nil t.leaves)) ≫ SumTree.chart A t
    rw [castOrder_map]
    exact SumTree.chart_right_unit A t
  | @tensor a b c d p q hp hq =>
    have na : a.leaves.Nodup := (List.nodup_append.mp hn).1
    have nc : c.leaves.Nodup := (List.nodup_append.mp hn).2.1
    change (p.evaluate A).hom ⊗ₘ (q.evaluate A).hom = SumTree.changeChart A (t:=.plus a c) (s:=.plus b d) (p.order.parallel q.order)
    rw [hp na, hq nc, SumTree.changeChart_parallel]
  | @seq a b c p q hp hq =>
    change (p.evaluate A).hom ≫ (q.evaluate A).hom = SumTree.changeChart A (.seq p.order q.order)
    rw [hp hn, hq (p.order.perm.nodup hn), SumTree.changeChart_comp]
  | @reverse a b p ih =>
    let e := p.evaluate A
    let q : AddressOrder X b.leaves a.leaves := (TensorCircuit.reverse p).order
    have hh := ih (p.order.perm.symm.nodup hn)
    change e.hom = SumTree.changeChart A p.order at hh
    have p₀ : SumTree.changeChart A q ≫ e.hom = 𝟙 (SumTree.eval A b) := by
      rw [hh, SumTree.changeChart_comp, SumTree.changeChart_coherent A hn _ (.ident b.leaves), SumTree.changeChart_id]
    apply (cancel_mono e.hom).mp
    exact e.inv_hom_id.trans p₀.symm

theorem coherent {a b : SumTree X} (p q : TensorCircuit X a b) (hn : a.leaves.Nodup) :
    (p.evaluate A).hom = (q.evaluate A).hom :=
  (normalize A p hn).trans ((SumTree.changeChart_coherent A hn p.order q.order).trans (normalize A q hn).symm)

end TensorCircuit

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
