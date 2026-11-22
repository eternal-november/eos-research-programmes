module
public import ContextualComposition.NativeRowRestriction

@[expose] public section
/-! Restriction along a native block selector. The restriction's actual
augmentation equation is the corresponding global composed block cell. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

theorem fibreRestrict_support {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (j : Fin l) : ∀ x ∈ fibreList (g ∘ f) j, f x ∈ fibreList g j :=
  fun x h => (mem_fibreList (f:=g) (i:=f x) (j:=j)).mpr ((mem_fibreList (f:=g ∘ f)).mp h)

theorem restricted_fibre {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l) (j : Fin l)
    {y : Fin m} (h : y ∈ fibreList g j) :
    wordFibre (fibreList (g ∘ f) j) f y = fibreList f y := by
  unfold wordFibre fibreList
  rw [List.filter_filter]
  apply congrArg (fun p => (List.finRange n).filter p)
  funext x
  have e := mem_fibreList.mp h
  change (decide (f x = y) && (g (f x) == j)) = (f x == y)
  by_cases t : f x = y <;> simp [t, e]

/-- Noninjective source carrier, occupied block with an empty destination
row, and a distinct block with no destination rows at all. -/
theorem restriction_addressed_empty_rows :
    let f : Fin 2 → Fin 2 := fun _ => 0
    let g : Fin 2 → Fin 2 := fun _ => 0
    fibreList g 0 = [0,1] ∧ fibreList (g ∘ f) 0 = [0,1] ∧
      wordFibre (fibreList (g ∘ f) 0) f 1 = [] ∧
      fibreList g 1 = [] ∧ fibreList (g ∘ f) 1 = [] := by
  decide

noncomputable def fibreRestrictNative {A B : Family C} (p : Hom ℙ A B) {l : Nat}
    (g : Fin B.n → Fin l) (j : Fin l) :
    Hom ℙ (wordFamily A.val (fibreList (g ∘ p.addr) j))
      (wordFamily B.val (fibreList g j)) :=
  wordNativeMap p.addr (fibreRestrict_support p.addr g j) (fibreList_nodup g j) A.val B.val
    (fun k => eqToHom (congrArg (fold 𝒮 Z A.val) (restricted_fibre p.addr g j (List.getElem_mem _))) ≫
      p.cell (fibreList g j)[k])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem fibreRestrict_cell_total {A B : Family C} (p : Hom ℙ A B) {l : Nat}
    (g : Fin B.n → Fin l) (j : Fin l) :
    let f := p.addr
    let a := fibreList (g ∘ f) j
    let b := fibreList g j
    let U := fibreRestrictNative p g j
    let E : totalFold (wordFamily A.val a) = fold 𝒮 Z A.val a :=
      (std_fold_map A.val (fun i => a[i]) (List.finRange a.length)).symm.trans
        (congrArg (fold 𝒮 Z A.val) (finRange_get a))
    let D : totalFold (wordFamily B.val b) = fold 𝒮 Z B.val b :=
      (std_fold_map B.val (fun i => b[i]) (List.finRange b.length)).symm.trans
        (congrArg (fold 𝒮 Z B.val) (finRange_get b))
    AddressOrder.mapSum additiveStructure (wordFamily A.val a).val (totalPartitionOrder U.addr) ≫
      rowsChart (wordFamily A.val a).val (fibreList U.addr) (List.finRange b.length) ≫
      act 𝒮 Z U.cell (List.finRange b.length) ≫ eqToHom D =
      eqToHom E ≫ standardPushSplit f g A.val j ≫ standardPushMap g p.cell j := by
  intro f a b U E D
  let X := fun i : Fin a.length => a[i]
  let Y := fun i : Fin b.length => b[i]
  let s := List.finRange a.length
  let t := List.finRange b.length
  let A₀ := fun i => A.val (X i)
  let L₀ := fibreList U.addr
  let L := fun i => fibreList f (Y i)
  let r := totalPartitionOrder U.addr
  let q := splitOrder f g j
  let K := fold 𝒮 Z A.val
  let r₀ := AddressOrder.mapSum additiveStructure A₀ r
  let q₀ := AddressOrder.mapSum additiveStructure A.val q
  let r₁ := rowsChart A₀ L₀ t
  let q₁ := rowsChart A.val L t
  let a₁ := act 𝒮 Z (fun i => p.cell (Y i)) t
  have h (i : Fin b.length) : (L₀ i).map X = L i :=
    (wordCarrier_fibre f (fibreRestrict_support f g j) (fibreList_nodup g j) i).trans
      (restricted_fibre f g j (List.getElem_mem _))
  let H (i : Fin b.length) : fold 𝒮 Z A₀ (L₀ i) = fold 𝒮 Z A.val (L i) :=
    (std_fold_map A.val X (L₀ i)).symm.trans (congrArg K (h i))
  let R := act 𝒮 Z (fun i => eqToHom (H i)) t
  let e : ((t.flatMap L₀).map X) = t.flatMap L :=
    (List.map_flatMap (f:=X) (g:=L₀) (l:=t)).trans
      (congrArg (fun M => t.flatMap M) (funext h))
  let k : t.flatMap L = b.flatMap (fibreList f) :=
    (List.flatMap_map Y (fibreList f) t).symm.trans
      (congrArg (fun w => w.flatMap (fibreList f)) (finRange_get b))
  let P : fold 𝒮 Z A₀ (t.flatMap L₀) = K (t.flatMap L) :=
    (std_fold_map A.val X (t.flatMap L₀)).symm.trans (congrArg K e)
  let Q : K (t.flatMap L) = K (b.flatMap (fibreList f)) := congrArg K k
  have h₀ : act 𝒮 Z U.cell t = R ≫ a₁ := by
    have hcell : U.cell = fun i => eqToHom (H i) ≫ p.cell (Y i) := by
      funext i
      change (eqToHom (wordCarrier_fibre_pin f _ _ A.val i) ≫
          (eqToHom (congrArg K (restricted_fibre f g j (List.getElem_mem _))) ≫ p.cell (Y i))) = _
      rw [← Category.assoc, eqToHom_trans]
    rw [hcell]
    exact (act_seq 𝒮 Z (fun i => eqToHom (H i)) (fun i => p.cell (Y i)) t).symm
  have h₁ : r₁ ≫ R = eqToHom P ≫ q₁ := rowsChart_relabel_input_inv A.val X L₀ h t
  have h₂ : q₁ ≫ a₁ ≫ eqToHom D =
      eqToHom Q ≫ rowsChart A.val (fibreList f) b ≫ act 𝒮 Z p.cell b :=
    rowsChart_index_apply A.val (fibreList f) Y p.cell t (finRange_get b)
  have h₃ : r₀ ≫ eqToHom (P.trans Q) = eqToHom E ≫ q₀ :=
    order_restrict_semantics A.val X s (t.flatMap L₀) (finRange_get a) (e.trans k)
      (fibreList_nodup (g ∘ f) j) q r
  change r₀ ≫ r₁ ≫ act 𝒮 Z U.cell t ≫ eqToHom D =
    eqToHom E ≫ (q₀ ≫ rowsChart A.val (fibreList f) b) ≫ act 𝒮 Z p.cell b
  rw [h₀]
  simp only [Category.assoc, reassoc_of% h₁, h₂]
  rw [← Category.assoc (eqToHom P), eqToHom_trans, ← Category.assoc r₀, h₃]
  simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
theorem wordAug_total {X : Type*} {I : C} (A : X → C) (xs : List X)
    (p : fold 𝒮 Z A xs ⟶ I) :
    wordAug A xs p = totalAug (wordFamily A xs)
      (eqToHom ((std_fold_map A (fun i => xs[i]) (List.finRange xs.length)).symm.trans
        (congrArg (fold 𝒮 Z A) (finRange_get xs))) ≫ p) := by
  apply congrArg (Aug.mk (wordFamily A xs))
  apply congrArg (Hom.mk (S:=ℙ) (A:=wordFamily A xs) (B:=terminalShape I) (terminalCarrier xs.length))
  funext j
  let A₀ := fun i : Fin xs.length => A xs[i]
  let e : standardPushObj (terminalCarrier xs.length) A₀ j = totalFold (wordFamily A xs) :=
    congrArg (fold 𝒮 Z A₀) (fibreList_terminal xs.length j)
  let f : totalFold (wordFamily A xs) = fold 𝒮 Z A xs :=
    (std_fold_map A (fun i => xs[i]) (List.finRange xs.length)).symm.trans
      (congrArg (fold 𝒮 Z A) (finRange_get xs))
  change eqToHom (e.trans f) ≫ p = eqToHom e ≫ eqToHom f ≫ p
  rw [← Category.assoc, eqToHom_trans]

theorem wordAug_total_ε {X : Type*} {I : C} (A : X → C) (xs : List X)
    (p : fold 𝒮 Z A xs ⟶ I) :
    (wordAug A xs p).ε = (totalAug (wordFamily A xs)
      (eqToHom ((std_fold_map A (fun i => xs[i]) (List.finRange xs.length)).symm.trans
        (congrArg (fold 𝒮 Z A) (finRange_get xs))) ≫ p)).ε := by
  apply congrArg (Hom.mk (S:=ℙ) (A:=wordFamily A xs) (B:=terminalShape I) (terminalCarrier xs.length))
  funext j
  let A₀ := fun i : Fin xs.length => A xs[i]
  let e : standardPushObj (terminalCarrier xs.length) A₀ j = totalFold (wordFamily A xs) :=
    congrArg (fold 𝒮 Z A₀) (fibreList_terminal xs.length j)
  let f : totalFold (wordFamily A xs) = fold 𝒮 Z A xs :=
    (std_fold_map A (fun i => xs[i]) (List.finRange xs.length)).symm.trans
      (congrArg (fold 𝒮 Z A) (finRange_get xs))
  change eqToHom (e.trans f) ≫ p = eqToHom e ≫ eqToHom f ≫ p
  rw [← Category.assoc, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
theorem fibreRestrict_aug_iff {A B : Family C} (p : Hom ℙ A B) {l : Nat}
    (g : Fin B.n → Fin l) (j : Fin l) {I : C}
    (α : standardPushObj (g ∘ p.addr) A.val j ⟶ I)
    (β : standardPushObj g B.val j ⟶ I) :
    (fibreRestrictNative p g j).comp (wordAug B.val (fibreList g j) β).ε =
      (wordAug A.val (fibreList (g ∘ p.addr) j) α).ε ↔
    standardPushSplit p.addr g A.val j ≫ standardPushMap g p.cell j ≫ β = α := by
  let a := fibreList (g ∘ p.addr) j
  let b := fibreList g j
  let f := p.addr
  let U := fibreRestrictNative p g j
  let e : totalFold (wordFamily A.val a) = standardPushObj (g ∘ f) A.val j :=
    (std_fold_map A.val (fun i => a[i]) (List.finRange a.length)).symm.trans
      (congrArg (fold 𝒮 Z A.val) (finRange_get a))
  let d : totalFold (wordFamily B.val b) = standardPushObj g B.val j :=
    (std_fold_map B.val (fun i => b[i]) (List.finRange b.length)).symm.trans
      (congrArg (fold 𝒮 Z B.val) (finRange_get b))
  let _ : IsIso (eqToHom e) := inferInstance
  let s := AddressOrder.mapSum additiveStructure (wordFamily A.val a).val (totalPartitionOrder U.addr)
  let r := rowsChart (wordFamily A.val a).val (fibreList U.addr) (List.finRange b.length)
  let P := act 𝒮 Z U.cell (List.finRange b.length)
  let Q := standardPushSplit f g A.val j
  let R := standardPushMap g p.cell j
  have h : s ≫ r ≫ P ≫ eqToHom d = eqToHom e ≫ Q ≫ R := fibreRestrict_cell_total p g j
  have ea : (wordAug A.val a α).ε = (totalAug (wordFamily A.val a) (eqToHom e ≫ α)).ε := by
    exact wordAug_total_ε A.val a α
  have eb : (wordAug B.val b β).ε = (totalAug (wordFamily B.val b) (eqToHom d ≫ β)).ε := by
    exact wordAug_total_ε B.val b β
  change U.comp (wordAug B.val b β).ε = (wordAug A.val a α).ε ↔ _
  rw [ea, eb, totalAug_preserving_iff]
  change (s ≫ r ≫ P ≫ eqToHom d ≫ β = eqToHom e ≫ α) ↔ _
  rw [← Category.assoc P, ← Category.assoc r, ← Category.assoc s, h]
  simp only [Category.assoc]
  exact cancel_epi (eqToHom e)

/-- Independent verification in each addressed block lifts to the single
actual global block morphism. The chosen final cells are still opaque and
may differ by block. Both empty blocks and globally empty families are
covered; no coproduct operation of the coefficient category is used. -/
theorem paste_native_blocks {A B D : Family C} (p : Hom ℙ A B) (q : Hom ℙ B D)
    (ρ : ∀ j, standardPushObj (q.addr ∘ p.addr) A.val j ⟶ D.val j)
    (h : ∀ j, (fibreRestrictNative p q.addr j).comp (wordAug B.val (fibreList q.addr j) (q.cell j)).ε =
      (wordAug A.val (fibreList (q.addr ∘ p.addr) j) (ρ j)).ε) :
    p.comp q = Hom.mk (S:=ℙ) (A:=A) (B:=D) (q.addr ∘ p.addr) ρ := by
  apply congrArg (Hom.mk (S:=ℙ) (A:=A) (B:=D) (q.addr ∘ p.addr))
  funext j
  exact (fibreRestrict_aug_iff p q.addr j (ρ j) (q.cell j)).mp (h j)

/-- The final stage is a single global augmentation of the block family,
not a family of augmentations from the source summands. -/
theorem paste_native_blocks_then_augment {A B D : Family C} {I : C}
    (p : Hom ℙ A B) (q : Hom ℙ B D)
    (ρ : ∀ j, standardPushObj (q.addr ∘ p.addr) A.val j ⟶ D.val j)
    (h : ∀ j, (fibreRestrictNative p q.addr j).comp (wordAug B.val (fibreList q.addr j) (q.cell j)).ε =
      (wordAug A.val (fibreList (q.addr ∘ p.addr) j) (ρ j)).ε)
    (ε : Hom ℙ D (terminalShape I)) :
    p.comp (q.comp ε) = (Hom.mk (S:=ℙ) (A:=A) (B:=D) (q.addr ∘ p.addr) ρ).comp ε := by
  rw [← Hom.comp_assoc, paste_native_blocks p q ρ h]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
