module
public import ContextualComposition.TaggedBlockSwap

@[expose] public section
/-! The actual standard symmetric finite direct image, including the
native split pentagon and both singleton units. Distinct address tags
are normalized before coefficient evaluation; zero is not initial. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem standardPushSplit_pent {n m l r : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (h : Fin l → Fin r) (A : Fin n → C) (k : Fin r) :
    standardPushSplit (g ∘ f) h A k ≫ standardPushMap h (standardPushSplit f g A) k =
      standardPushSplit f (h ∘ g) A k ≫ standardPushSplit g h (standardPushObj f A) k := by
  let P := fibreList h k
  let M := fibreList g
  let L := fibreList f
  let MN := fibreList (g ∘ f)
  let D := fun z => (M z).flatMap L
  let B := standardPushObj f A
  let Q := fun z => rowsChart A L (M z)
  let src := fibreList (h ∘ g ∘ f) k
  let dst := P.flatMap D
  let R {xs ys : List (Fin n)} (r : AddressOrder (Fin n) xs ys) :=
    AddressOrder.mapSum additiveStructure A r
  let p₁ := splitOrder (g ∘ f) h k
  let p₂ := rowOrders (fun z => splitOrder f g z) P
  let q₁ := splitOrder f (h ∘ g) k
  let q₂ := liftRows L (splitOrder g h k)
  let a : (P.flatMap M).flatMap L = dst := List.flatMap_assoc
  let q₃ := castOrder a
  let p : AddressOrder (Fin n) src dst := .seq p₁ p₂
  let q : AddressOrder (Fin n) src dst := .seq q₁ (.seq q₂ q₃)
  have eq : R p = R q := tagged_permutation_coherent A (fibreList_nodup _ _) p q
  have left_act : standardPushMap h (standardPushSplit f g A) k =
    act 𝒮 Z (fun z => R (splitOrder f g z)) P ≫ act 𝒮 Z Q P :=
      (act_seq 𝒮 Z (fun z => R (splitOrder f g z)) Q P).symm
  have left_row : R p₂ ≫ rowsChart A D P =
      rowsChart A MN P ≫ act 𝒮 Z (fun z => R (splitOrder f g z)) P :=
    rowsChart_rowOrders A (fun z => splitOrder f g z) P
  have right_row : R q₂ ≫ rowsChart A L (P.flatMap M) =
      rowsChart A L (fibreList (h ∘ g) k) ≫
        AddressOrder.mapSum additiveStructure B (splitOrder g h k) :=
    rowsChart_liftRows A L (splitOrder g h k)
  have iter : R q₃ ≫ rowsChart A D P ≫ act 𝒮 Z Q P =
      rowsChart A L (P.flatMap M) ≫ rowsChart B M P := by
    change AddressOrder.mapSum additiveStructure A (castOrder a) ≫ _ = _
    rw [castOrder_map]
    let A₀ := fold 𝒮 Z A
    let i : A₀ dst ⟶ A₀ ((P.flatMap M).flatMap L) := eqToHom (congrArg A₀ a.symm)
    let j : A₀ ((P.flatMap M).flatMap L) ⟶ A₀ dst := eqToHom (congrArg A₀ a)
    have e : i ≫ (rowsChart A L (P.flatMap M) ≫ rowsChart B M P) =
        rowsChart A D P ≫ act 𝒮 Z Q P := rowsChart_iterated A L M P
    have e' : j ≫ i = 𝟙 _ := by
      unfold j i
      rw [eqToHom_trans]
      rfl
    change j ≫ rowsChart A D P ≫ act 𝒮 Z Q P = _
    rw [← e, ← Category.assoc, e', Category.id_comp]
  change (R p₁ ≫ rowsChart A MN P) ≫ standardPushMap h (standardPushSplit f g A) k =
    (R q₁ ≫ rowsChart A L (fibreList (h ∘ g) k)) ≫
      (AddressOrder.mapSum additiveStructure B (splitOrder g h k) ≫ rowsChart B M P)
  rw [left_act]
  calc
    _ = R p ≫ rowsChart A D P ≫ act 𝒮 Z Q P := by
      have h := congrArg (fun t => R p₁ ≫ t ≫ act 𝒮 Z Q P) left_row
      change _ = (R p₁ ≫ R p₂) ≫ _
      simp only [Category.assoc] at h ⊢
      exact h.symm
    _ = R q ≫ rowsChart A D P ≫ act 𝒮 Z Q P := by rw [eq]
    _ = _ := by
      change (R q₁ ≫ (R q₂ ≫ R q₃)) ≫ _ = _
      simp only [Category.assoc]
      rw [iter]
      have h := congrArg (fun t => R q₁ ≫ t ≫ rowsChart B M P) right_row
      simp only [Category.assoc] at h
      exact h

/-- A standard symmetric additive monoidal operation induces the actual
native category of finite families and aggregated whole-fibre maps. -/
noncomputable def standardPush : Push (coeff (C:=C)) where
  obj := standardPushObj
  map := standardPushMap
  map_id f A := funext (standardPushMap_id f A)
  map_seq f := by
    intro _ _ _ p q
    exact funext (standardPushMap_comp f p q)
  single := standardPushSingle
  split := standardPushSplit
  single_nat p := funext (standardPushSingle_natural p)
  split_nat f g := by
    intro _ _ p
    exact funext (standardPushSplit_natural f g p)
  left_unit f A := funext (standardPushSplit_left_unit f A)
  right_unit f A := funext (standardPushSplit_right_unit f A)
  pent f g h A := funext (standardPushSplit_pent f g h A)


theorem standardPush_pinned :
    FoldPinned (standardPush (C:=C)) (fun xs => fold 𝒮 Z id xs) := by
  intro n m f A j
  change fold 𝒮 Z A (fibreList f j) = fold 𝒮 Z id ((fibreList f j).map A)
  generalize fibreList f j = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, fold, id_eq, ih]

instance rowsChart_iso {X Y : Type*} (A : X → C) (L : Y → List X) (ys : List Y) :
    IsIso (rowsChart A L ys) := by
  induction ys with
  | nil =>
    change IsIso (𝟙 Z)
    infer_instance
  | cons y ys ih =>
    let J : fold 𝒮 Z A (L y ++ ys.flatMap L) ⟶ fold 𝒮 Z A (L y) ⊗ fold 𝒮 Z A (ys.flatMap L) :=
      join additiveStructure A (L y) (ys.flatMap L)
    let v := joinInv SumTree.stdAddInvertible A (L y) (ys.flatMap L)
    let _ : IsIso J := ⟨v.inv, v.hi, v.ih⟩
    change IsIso (J ≫ (𝟙 (fold 𝒮 Z A (L y)) ⊗ₘ rowsChart A L ys))
    infer_instance

instance standardPushSplit_iso {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (A : Fin n → C) (j : Fin l) : IsIso (standardPushSplit f g A j) := by
  let p := AddressOrder.mapSum additiveStructure A (splitOrder f g j)
  let v := AddressOrder.mapSumInv (A:=A) SumTree.stdAddInvertible (splitOrder f g j)
  let _ : IsIso p := ⟨v.inv, v.hi, v.ih⟩
  change IsIso (p ≫ rowsChart A (fibreList f) (fibreList g j))
  infer_instance

instance standardPushSingle_iso {n : Nat} (A : Fin n → C) (j : Fin n) :
    IsIso (standardPushSingle A j) := by
  let e : standardPushObj id A j = A j ⊗ Z :=
    congrArg (fold 𝒮 Z A) (fibreList_id j)
  let p : standardPushObj id A j ⟶ A j ⊗ Z := eqToHom e
  let _ : IsIso p := inferInstanceAs (IsIso (eqToHom e))
  change IsIso (p ≫ (ρ_ (A j)).hom)
  infer_instance

/-- In a concrete two-to-two noninjective carrier, two equal coefficient
objects remain two occurrences; the other fibre is the additive unit. -/
theorem duplicate_labels_and_empty_fibre (a : C) :
    standardPushObj (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => a) (0 : Fin 2) =
        a ⊗ (a ⊗ Z) ∧
    standardPushObj (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => a) (1 : Fin 2) = Z := by
  constructor <;> rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
