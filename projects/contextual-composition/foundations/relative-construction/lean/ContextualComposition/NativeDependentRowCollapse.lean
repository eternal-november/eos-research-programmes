module
public import ContextualComposition.NativeDependentBlockTransport

@[expose] public section
/-! The original dependent augmentation factors through one native
collapse map over the parent projection, then the one outer augmentation.
Empty child rows still use their specified whole augmentation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush
local notation "𝒮" => binary (Additive.sum Additive.ofBraided)
local notation "Zₐ" => 𝟙_ _

variable {X Y : Type u} [DecidableEq X] {T : Bi (coeff (C:=C))}
variable (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
variable (xs : List X) (ys : X → List Y) (V : X → C) (W : X → Y → C)
variable (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I)

def rawDependentRowAug (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    (ys : X → List Y) (V : X → C) (W : X → Y → C)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (x : X) :
    fold 𝒮 Zₐ (dependentLabels (T:=T) V W) ((ys x).map (fun y => (x,y))) ⟶ V x :=
  eqToHom (std_fold_map (dependentLabels (T:=T) V W) (fun y => (x,y)) (ys x)) ≫
    (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)

noncomputable def nativeDependentRowCollapse (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    (xs : List X) (ys : X → List Y) (V : X → C) (W : X → Y → C)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (ys x) ⟶ I) (hn : xs.Nodup) :
    Hom ℙ (wordFamily (dependentLabels (T:=T) V W) (dependentWord xs ys)) (wordFamily V xs) :=
  wordNativeMap Prod.fst (outerBlock_support (us':=ys)) hn (dependentLabels (T:=T) V W) V
    (fun j => eqToHom (congrArg (fold 𝒮 Zₐ (dependentLabels (T:=T) V W))
      (targetParentBlockWord (us':=ys) hn (List.getElem_mem (l:=xs) (n:=j.val) _))) ≫
      rawDependentRowAug R L J ys V W δ xs[j])

set_option backward.isDefEq.respectTransparency false in
theorem nativeDependentRowCollapse_preserves (hn : xs.Nodup) (hw : (dependentWord xs ys).Nodup)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) :
    (nativeDependentRowCollapse R L J xs ys V W δ hn).comp (wordAug V xs ε).ε =
      (dependentWordAug R L J xs ys V W (fun x => eqToHom (std_fold_map id (W x) (ys x)) ≫ δ x) ε).ε := by
  let A := dependentLabels (T:=T) V W
  let F := fold 𝒮 Zₐ A
  let w := dependentWord xs ys
  let t := List.finRange xs.length
  let Y := fun i : Fin xs.length => xs[i]
  let P := fun x => (ys x).map (fun y => (x,y))
  let K := fun i : Fin xs.length => wordFibre w Prod.fst (Y i)
  let e (i : Fin xs.length) : K i = (P ∘ Y) i := targetParentBlockWord (us':=ys) hn (List.getElem_mem _)
  let e' := congrArg (fun k => t.flatMap k) (funext e)
  let p := rawDependentRowAug R L J ys V W δ
  let d := fun i => eqToHom (congrArg F (e i)) ≫ p (Y i)
  let ht : t.flatMap (P ∘ Y) = w :=
    (List.flatMap_map Y P t).symm.trans (congrArg (fun q => q.flatMap P) (finRange_get xs))
  let r := castOrder (ht.symm.trans e'.symm)
  let α := dependentWordAugCell R L J xs ys V W (fun x => eqToHom (std_fold_map id (W x) (ys x)) ≫ δ x) ε
  change (wordNativeMap Prod.fst (outerBlock_support (us':=ys)) hn A V d).comp (wordAug V xs ε).ε =
    (wordAug A w α).ε
  apply (wordNativeMap_preserving_iff Prod.fst (outerBlock_support (us':=ys)) hw hn A V d r α ε).mpr
  let c := fun i => eqToHom (congrArg F (e i))
  have h₁ : act 𝒮 Zₐ d t = act 𝒮 Zₐ c t ≫ act 𝒮 Zₐ (fun i => p (Y i)) t :=
    (act_seq 𝒮 Zₐ c _ t).symm
  have h₂ : rowsChart A K t ≫ act 𝒮 Zₐ c t = eqToHom (congrArg F e') ≫ rowsChart A (P ∘ Y) t :=
    rowsChart_rows_congr A e t
  have h₃ : rowsChart A (P ∘ Y) t ≫ act 𝒮 Zₐ (fun i => p (Y i)) t ≫ eqToHom (wordTotalPin V xs) =
      eqToHom (congrArg F ht) ≫ rowsChart A P xs ≫ act 𝒮 Zₐ p xs :=
    rowsChart_index_apply A P Y p t (finRange_get xs)
  change AddressOrder.mapSum additiveStructure A r ≫ rowsChart A K t ≫
    act 𝒮 Zₐ d t ≫ eqToHom (wordTotalPin V xs) ≫ ε = α
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃, castOrder_map]
  let a := congrArg F (ht.symm.trans e'.symm)
  let b := congrArg F e'
  let z := congrArg F ht
  have e₀ : eqToHom a ≫ eqToHom b ≫ eqToHom z = 𝟙 (F w) := by
    rw [← Category.assoc, eqToHom_trans, eqToHom_trans]
    rfl
  rw [reassoc_of% e₀]
  have h := dependentWordAug_raw_rows R L J xs ys V W δ ε
  change rowsChart A P xs ≫ act 𝒮 Zₐ p xs ≫ ε = α
  have hk := act_seq 𝒮 Zₐ (fun x => eqToHom (std_fold_map A (fun y => (x,y)) (ys x)))
    (fun x => (Lin.left L (V x)).collect (W x) (ys x) ≫ T.map (𝟙 (V x)) (δ x) ≫ J.ρ (V x)) xs
  refine Eq.trans ?_ h.symm
  have ho := congrArg (fun z => rowsChart A P xs ≫ z ≫ ε) hk.symm
  simp only [Category.assoc] at ho
  change rowsChart A P xs ≫ act 𝒮 Zₐ p xs ≫ ε = _
  unfold taggedRaggedRows
  simp only [Category.assoc]
  exact ho

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
