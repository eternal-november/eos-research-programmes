module
public import ContextualComposition.NativeIndependentWordChart

@[expose] public section
/-! Decode the *literal* terminal coefficient of an arbitrary native word
map. Every whole-fibre cell of that map remains the same opaque arrow. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

theorem wordTotalPin {X : Type w} (A : X → C) (xs : List X) :
    totalFold (wordFamily A xs) = fold 𝒮 Zₐ A xs :=
  (std_fold_map A (fun i => xs[i]) (List.finRange xs.length)).symm.trans
    (congrArg (fold 𝒮 Zₐ A) (finRange_get xs))

/-- Raw tag circuit induced by the literal ordered native partition,
not chosen by comparing resource labels or dropping empty rows. -/
noncomputable def wordNativePartitionOrder {X : Type w} {Y : Type z} [DecidableEq Y]
    {xs : List X} {ys : List Y} (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys) (hy : ys.Nodup) :
    AddressOrder X xs ((List.finRange ys.length).flatMap (fun i => wordFibre xs f ys[i])) := by
  let F := wordCarrier f h hy
  let get := fun i : Fin xs.length => xs[i]
  let t := List.finRange ys.length
  let r := (totalPartitionOrder F).relabel get
  let a := (finRange_get xs).symm
  have b : (t.flatMap (fibreList F)).map get = t.flatMap (fun i => wordFibre xs f ys[i]) :=
    (List.map_flatMap (f:=get) (g:=fibreList F) (l:=t)).trans
      (congrArg (fun D => t.flatMap D) (funext (wordCarrier_fibre f h hy)))
  exact .seq (castOrder a) (.seq r (castOrder b))

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_wordNativeMap {X : Type w} {Y : Type z} [DecidableEq Y]
    {xs : List X} {ys : List Y} (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys)
    (hx : xs.Nodup) (hy : ys.Nodup) (A : X → C) (B : Y → C)
    (p : ∀ i : Fin ys.length, fold 𝒮 Zₐ A (wordFibre xs f ys[i]) ⟶ B ys[i])
    (r : AddressOrder X xs ((List.finRange ys.length).flatMap (fun i => wordFibre xs f ys[i]))) :
    wholeContinuation (wordNativeMap f h hy A B p) ≫ eqToHom (wordTotalPin B ys) =
      eqToHom (wordTotalPin A xs) ≫ AddressOrder.mapSum additiveStructure A r ≫
        rowsChart A (fun i => wordFibre xs f ys[i]) (List.finRange ys.length) ≫
        act 𝒮 Zₐ p (List.finRange ys.length) ≫ eqToHom (wordTotalPin B ys) := by
  let q := wordNativeMap f h hy A B p
  let s := List.finRange xs.length
  let t := List.finRange ys.length
  let X₀ := fun i : Fin xs.length => xs[i]
  let A₀ := fun i => A (X₀ i)
  let L₀ := fibreList q.addr
  let L := fun i : Fin ys.length => wordFibre xs f ys[i]
  let F := fold 𝒮 Zₐ A
  let R := totalPartitionOrder q.addr
  let u := AddressOrder.mapSum additiveStructure A₀ R
  let v := AddressOrder.mapSum additiveStructure A r
  have e (i : Fin ys.length) : (L₀ i).map X₀ = L i := wordCarrier_fibre f h hy i
  let H (i : Fin ys.length) : fold 𝒮 Zₐ A₀ (L₀ i) = F (L i) :=
    (std_fold_map A X₀ (L₀ i)).symm.trans (congrArg F (e i))
  let a := act 𝒮 Zₐ (fun i => eqToHom (H i)) t
  let E : (t.flatMap L₀).map X₀ = t.flatMap L :=
    (List.map_flatMap (f:=X₀) (g:=L₀) (l:=t)).trans
      (congrArg (fun D => t.flatMap D) (funext e))
  let P : fold 𝒮 Zₐ A₀ (t.flatMap L₀) = F (t.flatMap L) :=
    (std_fold_map A X₀ (t.flatMap L₀)).symm.trans (congrArg F E)
  have h₀ : act 𝒮 Zₐ q.cell t = a ≫ act 𝒮 Zₐ p t :=
    (act_seq 𝒮 Zₐ (fun i => eqToHom (H i)) p t).symm
  have h₁ : rowsChart A₀ L₀ t ≫ a = eqToHom P ≫ rowsChart A L t :=
    rowsChart_relabel_input_inv A X₀ L₀ e t
  have h₂ : u ≫ eqToHom P = eqToHom (wordTotalPin A xs) ≫ v :=
    order_restrict_semantics A X₀ s (t.flatMap L₀) (finRange_get xs) E hx r R
  change (u ≫ rowsChart A₀ L₀ t ≫ act 𝒮 Zₐ q.cell t) ≫ eqToHom (wordTotalPin B ys) =
    eqToHom (wordTotalPin A xs) ≫ v ≫ rowsChart A L t ≫ act 𝒮 Zₐ p t ≫ eqToHom (wordTotalPin B ys)
  rw [h₀]
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂]

set_option backward.isDefEq.respectTransparency false in
/-- An augmentation test in the raw tag chart, with the *same* original
carrier-changing native arrow on the left. -/
theorem wordNativeMap_preserving_iff {X : Type w} {Y : Type z} [DecidableEq Y]
    {xs : List X} {ys : List Y} (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys)
    (hx : xs.Nodup) (hy : ys.Nodup) (A : X → C) (B : Y → C)
    (p : ∀ i : Fin ys.length, fold 𝒮 Zₐ A (wordFibre xs f ys[i]) ⟶ B ys[i])
    (r : AddressOrder X xs ((List.finRange ys.length).flatMap (fun i => wordFibre xs f ys[i])))
    {I : C} (α : fold 𝒮 Zₐ A xs ⟶ I) (β : fold 𝒮 Zₐ B ys ⟶ I) :
    (wordNativeMap f h hy A B p).comp (wordAug B ys β).ε = (wordAug A xs α).ε ↔
    AddressOrder.mapSum additiveStructure A r ≫
      rowsChart A (fun i => wordFibre xs f ys[i]) (List.finRange ys.length) ≫
      act 𝒮 Zₐ p (List.finRange ys.length) ≫ eqToHom (wordTotalPin B ys) ≫ β = α := by
  let q := wordNativeMap f h hy A B p
  let t := List.finRange ys.length
  let a := eqToHom (wordTotalPin A xs)
  let b := eqToHom (wordTotalPin B ys)
  let R := AddressOrder.mapSum additiveStructure A r
  let S := rowsChart A (fun i => wordFibre xs f ys[i]) t
  let P := act 𝒮 Zₐ p t
  let _ : IsIso a := inferInstanceAs (IsIso (eqToHom (wordTotalPin A xs)))
  change q.comp (wordAug B ys β).ε = (wordAug A xs α).ε ↔ R ≫ S ≫ P ≫ b ≫ β = α
  have ea : (wordAug A xs α).ε = (totalAug (wordFamily A xs) (a ≫ α)).ε := wordAug_total_ε A xs α
  have eb : (wordAug B ys β).ε = (totalAug (wordFamily B ys) (b ≫ β)).ε := wordAug_total_ε B ys β
  rw [ea, eb, totalAug_preserving_iff]
  have e : (wholeContinuation q ≫ b) ≫ β = (a ≫ R ≫ S ≫ P ≫ b) ≫ β :=
    congrArg (fun x => x ≫ β) (wholeContinuation_wordNativeMap f h hx hy A B p r)
  have e' : wholeContinuation q ≫ b ≫ β = a ≫ R ≫ S ≫ P ≫ b ≫ β := by
    simpa only [Category.assoc] using e
  unfold wholeContinuation at e'
  simp only [Category.assoc] at e'
  refine Iff.trans ?_ (cancel_epi a)
  exact ⟨fun h => e'.symm.trans h, fun h => e'.trans h⟩

set_option backward.isDefEq.respectTransparency false in
theorem wholeContinuation_native_raw_target {X : Type w} {Y : Type z} [DecidableEq Y]
    {xs : List X} {ys : List Y} (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys)
    (hx : xs.Nodup) (hy : ys.Nodup) (A : X → C) (B : Y → C)
    (p : ∀ y, fold 𝒮 Zₐ A (wordFibre xs f y) ⟶ B y)
    (r : AddressOrder X xs (ys.flatMap (wordFibre xs f))) :
    wholeContinuation (wordNativeMap f h hy A B (fun i => p ys[i])) ≫ eqToHom (wordTotalPin B ys) =
      eqToHom (wordTotalPin A xs) ≫ AddressOrder.mapSum additiveStructure A r ≫
        rowsChart A (wordFibre xs f) ys ≫ act 𝒮 Zₐ p ys := by
  let Y₀ := fun i : Fin ys.length => ys[i]
  let t := List.finRange ys.length
  let L := wordFibre xs f
  let F := fold 𝒮 Zₐ A
  let d : t.flatMap (L ∘ Y₀) = ys.flatMap L :=
    (List.flatMap_map Y₀ L t).symm.trans (congrArg (fun l => l.flatMap L) (finRange_get ys))
  let s := r.seq (castOrder d.symm)
  have e := wholeContinuation_wordNativeMap f h hx hy A B (fun i => p (Y₀ i)) s
  have e₀ : rowsChart A (L ∘ Y₀) t ≫ act 𝒮 Zₐ (fun i => p (Y₀ i)) t ≫ eqToHom (wordTotalPin B ys) =
      eqToHom (congrArg F d) ≫ rowsChart A L ys ≫ act 𝒮 Zₐ p ys :=
    rowsChart_index_apply A L Y₀ p t (finRange_get ys)
  have e₁ : AddressOrder.mapSum additiveStructure A s =
      AddressOrder.mapSum additiveStructure A r ≫ eqToHom (congrArg F d.symm) := by
    change AddressOrder.mapSum additiveStructure A r ≫ AddressOrder.mapSum additiveStructure A (castOrder d.symm) = _
    rw [castOrder_map]
  rw [e,e₁]
  simp only [Category.assoc]
  let v := AddressOrder.mapSum additiveStructure A r
  let a := eqToHom (wordTotalPin A xs)
  let u := eqToHom (congrArg F d.symm)
  have z := congrArg (fun k => a ≫ v ≫ u ≫ k) e₀
  refine z.trans ?_
  have c : eqToHom (congrArg F d.symm) ≫ eqToHom (congrArg F d) = 𝟙 (F (ys.flatMap L)) := by
    rw [eqToHom_trans]
    rfl
  change a ≫ v ≫ u ≫ eqToHom (congrArg F d) ≫ rowsChart A L ys ≫ act 𝒮 Zₐ p ys =
    a ≫ v ≫ rowsChart A L ys ≫ act 𝒮 Zₐ p ys
  rw [reassoc_of% c]

set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_raw_preserving_iff {X : Type w} {Y : Type z} [DecidableEq Y]
    {xs : List X} {ys : List Y} (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys)
    (hx : xs.Nodup) (hy : ys.Nodup) (A : X → C) (B : Y → C)
    (p : ∀ y, fold 𝒮 Zₐ A (wordFibre xs f y) ⟶ B y)
    (r : AddressOrder X xs (ys.flatMap (wordFibre xs f)))
    {I : C} (α : fold 𝒮 Zₐ A xs ⟶ I) (β : fold 𝒮 Zₐ B ys ⟶ I) :
    (wordNativeMap f h hy A B (fun i => p ys[i])).comp (wordAug B ys β).ε = (wordAug A xs α).ε ↔
    AddressOrder.mapSum additiveStructure A r ≫
      rowsChart A (wordFibre xs f) ys ≫ act 𝒮 Zₐ p ys ≫ β = α := by
  let q := wordNativeMap f h hy A B (fun i => p ys[i])
  let a := eqToHom (wordTotalPin A xs)
  let b := eqToHom (wordTotalPin B ys)
  let R := AddressOrder.mapSum additiveStructure A r
  let S := rowsChart A (wordFibre xs f) ys
  let P := act 𝒮 Zₐ p ys
  let _ : IsIso a := inferInstanceAs (IsIso (eqToHom (wordTotalPin A xs)))
  change q.comp (wordAug B ys β).ε = (wordAug A xs α).ε ↔ R ≫ S ≫ P ≫ β = α
  have ea : (wordAug A xs α).ε = (totalAug (wordFamily A xs) (a ≫ α)).ε := wordAug_total_ε A xs α
  have eb : (wordAug B ys β).ε = (totalAug (wordFamily B ys) (b ≫ β)).ε := wordAug_total_ε B ys β
  rw [ea, eb, totalAug_preserving_iff]
  have e : (wholeContinuation q ≫ b) ≫ β = (a ≫ R ≫ S ≫ P) ≫ β :=
    congrArg (fun x => x ≫ β) (wholeContinuation_native_raw_target f h hx hy A B p r)
  unfold wholeContinuation at e
  simp only [Category.assoc] at e
  refine Iff.trans ?_ (cancel_epi a)
  exact ⟨fun h => e.symm.trans h, fun h => e.trans h⟩

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
