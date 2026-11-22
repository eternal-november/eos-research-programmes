module
public import ContextualComposition.GridAddressBridge

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe w w'
variable {X : Type w} {Y : Type w'}

def AddressOrder.relabel (f : X → Y) {xs ys : List X} (p : AddressOrder X xs ys) :
    AddressOrder Y (xs.map f) (ys.map f) :=
  match p with
  | .ident _ => .ident _
  | .swap a b ts => .swap (f a) (f b) (ts.map f)
  | .keep a p => .keep (f a) (p.relabel f)
  | .seq p q => .seq (p.relabel f) (q.relabel f)

noncomputable def wordPositions (xs : List X) (h : xs.Nodup) : Fin xs.length ≃ {x // x ∈ xs} :=
  Equiv.ofBijective (fun i => ⟨xs[i], List.getElem_mem _⟩) ⟨by
    intro a b h'
    exact Fin.ext (h.getElem_inj.mp (congrArg Subtype.val h')), by
    intro ⟨x,hx⟩
    obtain ⟨i,hi,e⟩ := List.getElem_of_mem hx
    exact ⟨⟨i,hi⟩, Subtype.ext e⟩⟩

noncomputable def wordEquiv {xs ys : List X} (p : xs.Perm ys) (n : xs.Nodup) :
    Fin xs.length ≃ Fin ys.length :=
  (wordPositions xs n).trans ((⟨fun x => ⟨x.val,p.mem_iff.mp x.property⟩,
    fun x => ⟨x.val,p.mem_iff.mpr x.property⟩, fun _ => rfl, fun _ => rfl⟩ :
      {x // x ∈ xs} ≃ {y // y ∈ ys}).trans (wordPositions ys (p.nodup n)).symm)

theorem wordEquiv_get_symm {xs ys : List X} (p : xs.Perm ys) (n : xs.Nodup)
    (j : Fin ys.length) :
    xs[(wordEquiv p n).symm j] = ys[j] := by
  let e : {x // x ∈ xs} ≃ {y // y ∈ ys} :=
    ⟨fun x => ⟨x.val,p.mem_iff.mp x.property⟩,
     fun x => ⟨x.val,p.mem_iff.mpr x.property⟩, fun _ => rfl, fun _ => rfl⟩
  have h := (wordPositions xs n).apply_symm_apply (e.symm ((wordPositions ys (p.nodup n)) j))
  exact congrArg Subtype.val h

theorem finRange_get (xs : List X) :
    (List.finRange xs.length).map (fun i => xs[i]) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h h'
    simp only [List.getElem_map, List.getElem_finRange]
    rfl

end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w w'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {X : Type w} {Y : Type w'} (A : Y → C) (f : X → Y)
local notation "R" => AddressOrder.mapSum (additiveStructure (C:=C))
local notation "J" => fun xs => eqToHom (std_fold_map A f xs)

theorem std_fold_map_cons (x : X) (xs : List X) : J (x::xs) = A (f x) ◁ J xs := by
  rw [whiskerLeft_eqToHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem relabel_mapSum {xs ys : List X} (p : AddressOrder X xs ys) :
    J xs ≫ R (fun i => A (f i)) p = R A (p.relabel f) ≫ J ys := by
  induction p with
  | ident xs =>
    change J xs ≫ 𝟙 _ = 𝟙 _ ≫ J xs
    rw [Category.id_comp, Category.comp_id]
  | swap a b xs =>
    rw [std_fold_map_cons, std_fold_map_cons, std_fold_map_cons, std_fold_map_cons]
    let Q := fold 𝒮 Z A (xs.map f)
    let Q' := fold 𝒮 Z (fun x => A (f x)) xs
    let P := A (f a)
    let T := A (f b)
    change (P ◁ T ◁ J xs) ≫ ((α_ P T Q').inv ≫ ((β_ P T).hom ⊗ₘ 𝟙 Q') ≫ (α_ T P Q').hom) =
      ((α_ P T Q).inv ≫ ((β_ P T).hom ⊗ₘ 𝟙 Q) ≫ (α_ T P Q).hom) ≫ T ◁ P ◁ J xs
    rw [tensorHom_id, tensorHom_id]
    exact (crossHead_nat P T (J xs)).symm
  | keep a p ih =>
    rw [std_fold_map_cons, std_fold_map_cons]
    change (A (f a) ◁ J _) ≫ (𝟙 _ ⊗ₘ R (fun i => A (f i)) p) =
      (𝟙 _ ⊗ₘ R A (p.relabel f)) ≫ (A (f a) ◁ J _)
    rw [id_tensorHom, id_tensorHom, ← whiskerLeft_comp, ← whiskerLeft_comp, ih]
  | seq p q hp hq =>
    change J _ ≫ (R (fun i => A (f i)) p ≫ R (fun i => A (f i)) q) =
      (R A (p.relabel f) ≫ R A (q.relabel f)) ≫ J _
    rw [← Category.assoc, hp, Category.assoc, hq, Category.assoc]


variable {B : Y → C}
set_option backward.isDefEq.respectTransparency false in
theorem std_act_map (p : ∀ y, A y ⟶ B y) (xs : List X) :
    J xs ≫ act 𝒮 Z (fun x => p (f x)) xs =
      act 𝒮 Z p (xs.map f) ≫ eqToHom (std_fold_map B f xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    let P := act 𝒮 Z (fun x => p (f x)) xs
    let Q := act 𝒮 Z p (xs.map f)
    have e₁ := std_fold_map_cons A f a xs
    have e₂ := std_fold_map_cons B f a xs
    calc
      _ = (A (f a) ◁ J xs) ≫ (p (f a) ⊗ₘ P) :=
        congrArg (fun u => u ≫ (p (f a) ⊗ₘ P)) e₁
      _ = (p (f a) ⊗ₘ Q) ≫ B (f a) ◁ eqToHom (std_fold_map B f xs) := by
        rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          Category.id_comp, Category.comp_id, ih]
      _ = _ := (congrArg (fun u => (p (f a) ⊗ₘ Q) ≫ u) e₂).symm

set_option backward.isDefEq.respectTransparency false in
theorem std_act_eqToHom {A B : X → C} (E : ∀ x, A x = B x) (xs : List X) :
    act 𝒮 Z (fun x => eqToHom (E x)) xs =
      eqToHom (congrArg (fun F => fold 𝒮 Z F xs) (funext E)) := by
  have e := funext E
  cases e
  change act 𝒮 Z (fun x => 𝟙 (A x)) xs = 𝟙 _
  exact occurrence_act_id A xs

def wordFamily (A : Y → C) (xs : List Y) : Family C :=
  ⟨xs.length, fun i => A xs[i]⟩

def terminalCarrier (n : Nat) : Fin n → Fin 1 := fun _ => 0

theorem fibreList_terminal (n : Nat) (j : Fin 1) :
    fibreList (terminalCarrier n) j = List.finRange n := by
  have h : j = 0 := Subsingleton.elim _ _
  subst j
  simp [fibreList, terminalCarrier]

theorem wordFoldPin (A : Y → C) (xs : List Y) (j : Fin 1) :
    standardPushObj (terminalCarrier xs.length) (wordFamily A xs).val j =
      fold 𝒮 Z A xs := by
  change fold 𝒮 Z (fun i : Fin xs.length => A xs[i]) (fibreList (terminalCarrier xs.length) j) = _
  rw [fibreList_terminal]
  let a (i : Fin xs.length) := xs[i]
  exact (std_fold_map A a (List.finRange xs.length)).symm.trans
    (congrArg (fold 𝒮 Z A) (finRange_get xs))

noncomputable def wordAug {I : C} (A : Y → C) (xs : List Y) (a : fold 𝒮 Z A xs ⟶ I) : Aug ℙ I where
  base := wordFamily A xs
  ε := ⟨terminalCarrier xs.length, fun j => eqToHom (wordFoldPin A xs j) ≫ a⟩

theorem nativeEquivOrder {n m : Nat} (e : Fin n ≃ Fin m) :
    (List.finRange n).Perm ((List.finRange m).map e.symm) := by
  have h : ((List.finRange m).map e.symm).Nodup :=
    (List.nodup_finRange m).map e.symm (fun _ _ h eq => h (e.symm.injective eq))
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange n) h).mpr
  intro i
  simp only [List.mem_finRange, List.mem_map, true_iff, true_and]
  exact ⟨e i, e.symm_apply_apply i⟩

noncomputable def wordComparisonCells (A B : Y → C) {xs ys : List Y}
    (p : AddressOrder Y xs ys) (hn : xs.Nodup) (φ : ∀ y, A y ≅ B y) :
    ∀ j, (wordFamily A xs).val ((wordEquiv p.perm hn).symm j) ≅ (wordFamily B ys).val j :=
  fun j => eqToIso (congrArg A (wordEquiv_get_symm p.perm hn j)) ≪≫ φ ys[j]


set_option backward.isDefEq.respectTransparency false in
theorem relabel_mapSum_inv {xs ys : List X} (p : AddressOrder X xs ys) :
    R (fun i => A (f i)) p ≫ eqToHom (std_fold_map A f ys).symm =
      eqToHom (std_fold_map A f xs).symm ≫ R A (p.relabel f) := by
  let d := eqToHom (std_fold_map A f xs).symm
  let e := eqToHom (std_fold_map A f ys).symm
  have h₀ : d ≫ J xs = 𝟙 _ := by unfold d; rw [eqToHom_trans]; rfl
  have h₁ : J ys ≫ e = 𝟙 _ := by unfold e; rw [eqToHom_trans]; rfl
  have h := congrArg (fun r => d ≫ r ≫ e) (relabel_mapSum A f p)
  simp only [Category.assoc] at h
  rw [reassoc_of% h₀, h₁] at h
  change _ = d ≫ _
  exact h.trans (congrArg (fun t => d ≫ t) (Category.comp_id _))

set_option backward.isDefEq.respectTransparency false in
theorem wordOrder_semantics {xs ys : List Y} (p : AddressOrder Y xs ys) (hn : xs.Nodup)
    (l : List (Fin xs.length)) (m : List (Fin ys.length))
    (hl : l.map (fun i => xs[i]) = xs) (hm : m.map (fun j => ys[j]) = ys)
    (r : AddressOrder (Fin xs.length) l (m.map (wordEquiv p.perm hn).symm)) :
    let e := wordEquiv p.perm hn
    let h : (m.map e.symm).map (fun i => xs[i]) = ys := by
      rw [List.map_map]
      exact (congrArg (fun g => m.map g)
        (funext (wordEquiv_get_symm p.perm hn))).trans hm
    R (wordFamily A xs).val r ≫ eqToHom ((std_fold_map A (fun i => xs[i]) (m.map e.symm)).symm.trans
      (congrArg (fold 𝒮 Z A) h)) =
    eqToHom ((std_fold_map A (fun i => xs[i]) l).symm.trans (congrArg (fold 𝒮 Z A) hl)) ≫ R A p := by
  intro e ht
  let G := fold 𝒮 Z A
  let g (i : Fin xs.length) : Y := xs[i]
  let q : AddressOrder Y xs ys :=
    .seq (castOrder hl.symm) (.seq (r.relabel g) (castOrder ht))
  have eq := tagged_permutation_coherent A hn q p
  have eq' : eqToHom (congrArg G hl.symm) ≫ R A (r.relabel g) ≫ eqToHom (congrArg G ht) = R A p := by
    change R A (castOrder hl.symm) ≫ (R A (r.relabel g) ≫ R A (castOrder ht)) = _ at eq
    rw [castOrder_map, castOrder_map] at eq
    exact eq
  have E : R A (r.relabel g) ≫ eqToHom (congrArg G ht) = eqToHom (congrArg G hl) ≫ R A p := by
    have t := congrArg (fun u => eqToHom (congrArg G hl) ≫ u) eq'
    rw [← Category.assoc, eqToHom_trans] at t
    have z : eqToHom ((congrArg G hl).trans (congrArg G hl.symm)) = 𝟙 (G (l.map g)) := rfl
    rw [z, Category.id_comp] at t
    exact t
  let j₁ := (std_fold_map A g (m.map e.symm)).symm
  let j₀ := (std_fold_map A g l).symm
  let s₁ := congrArg G ht
  let s₀ := congrArg G hl
  have h := relabel_mapSum_inv A g r
  change R (fun i => A (g i)) r ≫ eqToHom (j₁.trans s₁) = eqToHom (j₀.trans s₀) ≫ R A p
  rw [← eqToHom_trans j₁ s₁, ← eqToHom_trans j₀ s₀, ← Category.assoc, h, Category.assoc,
    Category.assoc, E]


set_option backward.isDefEq.respectTransparency false in
theorem std_act_list_congr {A B : Y → C} (p : ∀ y, A y ⟶ B y) {xs ys : List Y} (e : xs = ys) :
    act 𝒮 Z p xs ≫ eqToHom (congrArg (fold 𝒮 Z B) e) =
      eqToHom (congrArg (fold 𝒮 Z A) e) ≫ act 𝒮 Z p ys := by
  cases e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem wordCells_semantics {xs ys : List Y} (B : Y → C) (p : AddressOrder Y xs ys) (hn : xs.Nodup)
    (φ : ∀ y, A y ≅ B y) (m : List (Fin ys.length)) (hm : m.map (fun j => ys[j]) = ys) :
    let e := wordEquiv p.perm hn
    let h : (m.map e.symm).map (fun i => xs[i]) = ys := by
      rw [List.map_map]
      exact (congrArg (fun g => m.map g)
        (funext (wordEquiv_get_symm p.perm hn))).trans hm
    eqToHom (std_fold_map (wordFamily A xs).val e.symm m) ≫
      act 𝒮 Z (fun j => (wordComparisonCells A B p hn φ j).hom) m ≫
      eqToHom ((std_fold_map B (fun j => ys[j]) m).symm.trans (congrArg (fold 𝒮 Z B) hm)) =
    eqToHom ((std_fold_map A (fun i => xs[i]) (m.map e.symm)).symm.trans
      (congrArg (fold 𝒮 Z A) h)) ≫ act 𝒮 Z (fun y => (φ y).hom) ys := by
  intro e ht
  let src (i : Fin xs.length) := A xs[i]
  let y (j : Fin ys.length) := ys[j]
  let P : ∀ j : Fin ys.length, src (e.symm j) = A (y j) :=
    fun j => congrArg A (wordEquiv_get_symm p.perm hn j)
  let cell := fun j => (φ (y j)).hom
  let raw := fun y => (φ y).hom
  let W := fold 𝒮 Z (fun j => src (e.symm j)) m
  let W' := fold 𝒮 Z (fun j => A (y j)) m
  let i : fold 𝒮 Z src (m.map e.symm) = W := std_fold_map src e.symm m
  let g : W = W' := congrArg (fun F => fold 𝒮 Z F m) (funext P)
  let j : fold 𝒮 Z A (m.map y) = W' := std_fold_map A y m
  let j' : fold 𝒮 Z B (m.map y) = fold 𝒮 Z (fun j => B (y j)) m := std_fold_map B y m
  let a : fold 𝒮 Z A (m.map y) = fold 𝒮 Z A ys := congrArg (fold 𝒮 Z A) hm
  let b : fold 𝒮 Z B (m.map y) = fold 𝒮 Z B ys := congrArg (fold 𝒮 Z B) hm
  let out : fold 𝒮 Z src (m.map e.symm) = fold 𝒮 Z A ys := (std_fold_map A (fun i => xs[i])
    (m.map e.symm)).symm.trans (congrArg (fold 𝒮 Z A) ht)
  have h₁ : act 𝒮 Z (fun j => eqToHom (P j) ≫ cell j) m =
      eqToHom g ≫ act 𝒮 Z cell m :=
    (act_seq 𝒮 Z (fun j => eqToHom (P j)) cell m).symm.trans
      (congrArg (fun f => f ≫ act 𝒮 Z cell m) (std_act_eqToHom P m))
  have h₂ : eqToHom j ≫ act 𝒮 Z cell m = act 𝒮 Z raw (m.map y) ≫ eqToHom j' :=
    std_act_map A y raw m
  have h₃ : act 𝒮 Z raw (m.map y) ≫ eqToHom b = eqToHom a ≫ act 𝒮 Z raw ys :=
    std_act_list_congr raw hm
  have i' : eqToHom i ≫ eqToHom g = eqToHom (out.trans (a.symm.trans j)) := by
    rw [eqToHom_trans]
  have j'i : eqToHom j' ≫ eqToHom (j'.symm.trans b) = eqToHom b := by
    rw [eqToHom_trans]
  have ai : eqToHom (out.trans a.symm) ≫ eqToHom a = eqToHom out := by
    rw [eqToHom_trans]
  change eqToHom i ≫ act 𝒮 Z (fun j => eqToHom (P j) ≫ cell j) m ≫
      eqToHom (j'.symm.trans b) = eqToHom out ≫ act 𝒮 Z raw ys
  rw [h₁, ← Category.assoc, ← Category.assoc, i', ← eqToHom_trans (out.trans a.symm) j,
    Category.assoc]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, j'i, h₃, ← Category.assoc, ai]


set_option backward.isDefEq.respectTransparency false in
theorem wordAug_preserving {I : C} {xs ys : List Y} (B : Y → C) (p : AddressOrder Y xs ys)
    (hn : xs.Nodup) (φ : ∀ y, A y ≅ B y) (a : fold 𝒮 Z A xs ⟶ I)
    (b : fold 𝒮 Z B ys ⟶ I)
    (preserves : R A p ≫ act 𝒮 Z (fun y => (φ y).hom) ys ≫ b = a) :
    Hom.comp (nativeReindex (wordEquiv p.perm hn) (wordComparisonCells A B p hn φ))
      (wordAug B ys b).ε = (wordAug A xs a).ε := by
  apply native_hom_ext rfl
  intro j
  let e := wordEquiv p.perm hn
  let A₁ : Fin xs.length → C := (wordFamily A xs).val
  let B₁ : Fin ys.length → C := (wordFamily B ys).val
  let f := terminalCarrier ys.length
  let c := fun j => (wordComparisonCells A B p hn φ j).hom
  let l := fibreList (f ∘ e) j
  let m := fibreList f j
  have el : l = List.finRange xs.length := fibreList_terminal _ _
  have em : m = List.finRange ys.length := fibreList_terminal _ _
  let r : AddressOrder (Fin xs.length) l (m.map e.symm) :=
    .seq (castOrder el) (.seq (Classical.choice (AddressOrder.ofPerm (nativeEquivOrder e)))
      (castOrder (congrArg (List.map e.symm) em.symm)))
  have hl : l.map (fun i => xs[i]) = xs := (congrArg (List.map (fun i => xs[i])) el).trans (finRange_get xs)
  have hm : m.map (fun i => ys[i]) = ys := (congrArg (List.map (fun i => ys[i])) em).trans (finRange_get ys)
  have htm : (m.map e.symm).map (fun i => xs[i]) = ys := by
    rw [List.map_map]
    exact (congrArg (fun g => m.map g) (funext (wordEquiv_get_symm p.perm hn))).trans hm
  let f₀ : standardPushObj (f ∘ e) A₁ j = fold 𝒮 Z A xs := wordFoldPin A xs j
  let f₁ : standardPushObj f B₁ j = fold 𝒮 Z B ys := wordFoldPin B ys j
  let f₂ : fold 𝒮 Z A₁ (m.map e.symm) = fold 𝒮 Z A ys :=
    (std_fold_map A (fun i => xs[i]) (m.map e.symm)).symm.trans (congrArg (fold 𝒮 Z A) htm)
  let g : fold 𝒮 Z A₁ (m.map e.symm) = standardPushObj f (fun y => A₁ (e.symm y)) j :=
    std_fold_map A₁ e.symm m
  have l₁ : R A₁ r ≫ eqToHom f₂ = eqToHom f₀ ≫ R A p := wordOrder_semantics A p hn l m hl hm r
  have l₂ : eqToHom g ≫ standardPushMap f c j ≫ eqToHom f₁ =
      eqToHom f₂ ≫ act 𝒮 Z (fun y => (φ y).hom) ys :=
    wordCells_semantics A B p hn φ m hm
  have h := standardPush_equiv_collapse e f A₁ B₁ c j r
  change standardPushSplit e f A₁ j ≫ (standardPushMap f (fun y => reindexSingleton e A₁ y ≫ c y) j ≫
    (eqToHom f₁ ≫ b)) = 𝟙 _ ≫ (eqToHom f₀ ≫ a)
  rw [Category.id_comp, ← Category.assoc, h]
  change (R A₁ r ≫ eqToHom g ≫ standardPushMap f c j) ≫ eqToHom f₁ ≫ b = _
  simp only [Category.assoc]
  rw [reassoc_of% l₂, ← Category.assoc (R A₁ r), l₁]
  simp only [Category.assoc]
  exact congrArg (fun t => eqToHom f₀ ≫ t) preserves

/-- Realize an ordered tagged augmentation comparison as a literal
isomorphism of augmented native finite families. -/
noncomputable def wordAugIso {I : C} {xs ys : List Y} (B : Y → C) (p : AddressOrder Y xs ys)
    (hn : xs.Nodup) (φ : ∀ y, A y ≅ B y) (a : fold 𝒮 Z A xs ⟶ I)
    (b : fold 𝒮 Z B ys ⟶ I)
    (preserves : R A p ≫ act 𝒮 Z (fun y => (φ y).hom) ys ≫ b = a) :
    NativeAugmentedIso (wordAug A xs a) (wordAug B ys b) :=
  nativeReindexAugIso (wordEquiv p.perm hn) (wordComparisonCells A B p hn φ)
    (wordAug_preserving A B p hn φ a b preserves)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
