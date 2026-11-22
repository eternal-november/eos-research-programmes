module
public import ContextualComposition.NativeReindexSquare

@[expose] public section
/-! Assemble genuine native carrier-changing arrows from whole addressed
fibre maps. The carrier map need not be injective; a fibre with no entries
still requires an actual arrow from the chosen additive unit. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w w'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {X : Type w} {Y : Type w'} {xs : List X} {ys : List Y}
variable (f : X → Y) (h : ∀ x ∈ xs, f x ∈ ys) (hy : ys.Nodup)

noncomputable def wordCarrier (i : Fin xs.length) : Fin ys.length :=
  (wordPositions ys hy).symm ⟨f xs[i], h _ (List.getElem_mem _)⟩

theorem wordCarrier_get (i : Fin xs.length) :
    ys[wordCarrier f h hy i] = f xs[i] := by
  have e := (wordPositions ys hy).apply_symm_apply ⟨f xs[i], h _ (List.getElem_mem _)⟩
  exact congrArg Subtype.val e

theorem wordCarrier_eq_iff (i : Fin xs.length) (j : Fin ys.length) :
    wordCarrier f h hy i = j ↔ f xs[i] = ys[j] := by
  constructor
  · intro eq
    exact (wordCarrier_get f h hy i).symm.trans (congrArg (fun j : Fin ys.length => ys[j]) eq)
  · intro eq
    exact Fin.ext (hy.getElem_inj.mp ((wordCarrier_get f h hy i).trans eq))

variable [DecidableEq Y]
def wordFibre (xs : List X) (f : X → Y) (y : Y) : List X :=
  xs.filter (fun x => decide (f x = y))

theorem wordCarrier_fibre (j : Fin ys.length) :
    (fibreList (wordCarrier f h hy) j).map (fun i => xs[i]) = wordFibre xs f ys[j] := by
  let P (x : X) := decide (f x = ys[j])
  let g (i : Fin xs.length) := xs[i]
  let l := List.finRange xs.length
  change (l.filter (fun i => wordCarrier f h hy i == j)).map g = xs.filter P
  calc
    _ = (l.filter (fun i => P (g i))).map g := by
      apply congrArg (fun p => (l.filter p).map g)
      funext i
      simp only [P, g, beq_eq_decide, wordCarrier_eq_iff]
    _ = (l.map g).filter P := (List.filter_map (f:=g) (p:=P) (l:=l)).symm
    _ = _ := congrArg (List.filter P) (finRange_get xs)

variable (A : X → C) (B : Y → C)
theorem wordCarrier_fibre_pin (j : Fin ys.length) :
    standardPushObj (wordCarrier f h hy) (wordFamily A xs).val j =
      fold 𝒮 Z A (wordFibre xs f ys[j]) :=
  (std_fold_map A (fun i : Fin xs.length => xs[i]) (fibreList (wordCarrier f h hy) j)).symm.trans
    (congrArg (fold 𝒮 Z A) (wordCarrier_fibre f h hy j))

/-- An actual native whole-fibre arrow. Unlike an isomorphism over a
carrier equivalence, neither injectivity nor invertibility is required. -/
noncomputable def wordNativeMap
    (p : ∀ j : Fin ys.length, fold 𝒮 Z A (wordFibre xs f ys[j]) ⟶ B ys[j]) :
    Hom ℙ (wordFamily A xs) (wordFamily B ys) :=
  ⟨wordCarrier f h hy, fun j => eqToHom (wordCarrier_fibre_pin f h hy A j) ≫ p j⟩


variable {X' : Type w} {Y' : Type w'}
variable {xs' : List X} {ys' : List Y}

/-- Canonical whole-fibre reordering from restricting a global tagged
word reordering. No fibre coefficient labels participate in selection. -/
noncomputable def wordFibreOrder (f : X → Y) (p : AddressOrder X xs xs') (y : Y) :
    AddressOrder X (wordFibre xs f y) (wordFibre xs' f y) :=
  Classical.choice (AddressOrder.ofPerm (p.perm.filter (fun x => decide (f x = y))))

theorem wordEquiv_get {xs ys : List X} (p : xs.Perm ys) (n : xs.Nodup) (i : Fin xs.length) :
    ys[wordEquiv p n i] = xs[i] := by
  have h := wordEquiv_get_symm p n (wordEquiv p n i)
  have h' := congrArg (fun j : Fin xs.length => xs[j]) ((wordEquiv p n).symm_apply_apply i)
  exact h.symm.trans h'

omit [DecidableEq Y] in
/-- Matching the same raw tag across two presentations really commutes
with a changing native carrier, even when it is noninjective. -/
theorem wordCarrier_square {f : X → Y} (ps : AddressOrder X xs xs') (pt : AddressOrder Y ys ys')
    (hx : xs.Nodup) (hy : ys.Nodup)
    (h : ∀ x ∈ xs, f x ∈ ys) (h' : ∀ x ∈ xs', f x ∈ ys') :
    (wordEquiv pt.perm hy : Fin ys.length → Fin ys'.length) ∘ wordCarrier f h hy =
      wordCarrier f h' (pt.perm.nodup hy) ∘ wordEquiv ps.perm hx := by
  funext i
  apply Fin.ext
  apply (pt.perm.nodup hy).getElem_inj.mp
  change ys'[wordEquiv pt.perm hy (wordCarrier f h hy i)] =
    ys'[wordCarrier f h' (pt.perm.nodup hy) (wordEquiv ps.perm hx i)]
  rw [wordEquiv_get, wordCarrier_get, wordCarrier_get, wordEquiv_get]


section FibreSemantics
variable (A : X → C)

set_option backward.isDefEq.respectTransparency false in
theorem order_restrict_semantics {n : Nat} (g : Fin n → X) (l m : List (Fin n))
    {as bs : List X} (ha : l.map g = as) (hb : m.map g = bs)
    (hn : as.Nodup) (p : AddressOrder X as bs) (r : AddressOrder (Fin n) l m) :
    AddressOrder.mapSum additiveStructure (fun k => A (g k)) r ≫
      eqToHom ((std_fold_map A g m).symm.trans (congrArg (fold 𝒮 Z A) hb)) =
    eqToHom ((std_fold_map A g l).symm.trans (congrArg (fold 𝒮 Z A) ha)) ≫
      AddressOrder.mapSum additiveStructure A p := by
  let F := fold 𝒮 Z A
  let R := fun {xs ys} (r : AddressOrder X xs ys) => AddressOrder.mapSum additiveStructure A r
  let q : AddressOrder X as bs := .seq (castOrder ha.symm) (.seq (r.relabel g) (castOrder hb))
  have eq := tagged_permutation_coherent A hn q p
  change R (castOrder ha.symm) ≫ (R (r.relabel g) ≫ R (castOrder hb)) = R p at eq
  dsimp only [R] at eq
  rw [castOrder_map, castOrder_map] at eq
  have E : R (r.relabel g) ≫ eqToHom (congrArg F hb) =
      eqToHom (congrArg F ha) ≫ R p := by
    have t := congrArg (fun u => eqToHom (congrArg F ha) ≫ u) eq
    rw [← Category.assoc, eqToHom_trans] at t
    have z : eqToHom ((congrArg F ha).trans (congrArg F ha.symm)) = 𝟙 (F (l.map g)) := rfl
    rw [z, Category.id_comp] at t
    exact t
  let j₁ := (std_fold_map A g m).symm
  let j₀ := (std_fold_map A g l).symm
  let s₁ := congrArg F hb
  let s₀ := congrArg F ha
  have h := relabel_mapSum_inv A g r
  change AddressOrder.mapSum additiveStructure (fun i => A (g i)) r ≫ eqToHom (j₁.trans s₁) =
    eqToHom (j₀.trans s₀) ≫ R p
  rw [← eqToHom_trans j₁ s₁, ← eqToHom_trans j₀ s₀, ← Category.assoc, h,
    Category.assoc, Category.assoc, E]

set_option backward.isDefEq.respectTransparency false in
theorem wordCells_local_semantics {xs ys ws : List X} (B : X → C) (p : AddressOrder X xs ys) (hn : xs.Nodup)
    (φ : ∀ y : X, A y ≅ B y) (m : List (Fin ys.length)) (hm : m.map (fun j => ys[j]) = ws) :
    let e := wordEquiv p.perm hn
    let h : (m.map e.symm).map (fun i => xs[i]) = ws := by
      rw [List.map_map]
      exact (congrArg (fun g => m.map g)
        (funext (wordEquiv_get_symm p.perm hn))).trans hm
    eqToHom (std_fold_map (wordFamily A xs).val e.symm m) ≫
      act 𝒮 Z (fun j => (wordComparisonCells A B p hn φ j).hom) m ≫
      eqToHom ((std_fold_map B (fun j => ys[j]) m).symm.trans (congrArg (fold 𝒮 Z B) hm)) =
    eqToHom ((std_fold_map A (fun i => xs[i]) (m.map e.symm)).symm.trans
      (congrArg (fold 𝒮 Z A) h)) ≫ act 𝒮 Z (fun y => (φ y).hom) ws := by
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
  let a : fold 𝒮 Z A (m.map y) = fold 𝒮 Z A ws := congrArg (fold 𝒮 Z A) hm
  let b : fold 𝒮 Z B (m.map y) = fold 𝒮 Z B ws := congrArg (fold 𝒮 Z B) hm
  let out : fold 𝒮 Z src (m.map e.symm) = fold 𝒮 Z A ws := (std_fold_map A (fun i => xs[i])
    (m.map e.symm)).symm.trans (congrArg (fold 𝒮 Z A) ht)
  have h₁ : act 𝒮 Z (fun j => eqToHom (P j) ≫ cell j) m =
      eqToHom g ≫ act 𝒮 Z cell m :=
    (act_seq 𝒮 Z (fun j => eqToHom (P j)) cell m).symm.trans
      (congrArg (fun f => f ≫ act 𝒮 Z cell m) (std_act_eqToHom P m))
  have h₂ : eqToHom j ≫ act 𝒮 Z cell m = act 𝒮 Z raw (m.map y) ≫ eqToHom j' :=
    std_act_map A y raw m
  have h₃ : act 𝒮 Z raw (m.map y) ≫ eqToHom b = eqToHom a ≫ act 𝒮 Z raw ws :=
    std_act_list_congr raw hm
  have i' : eqToHom i ≫ eqToHom g = eqToHom (out.trans (a.symm.trans j)) := by
    rw [eqToHom_trans]
  have j'i : eqToHom j' ≫ eqToHom (j'.symm.trans b) = eqToHom b := by
    rw [eqToHom_trans]
  have ai : eqToHom (out.trans a.symm) ≫ eqToHom a = eqToHom out := by
    rw [eqToHom_trans]
  change eqToHom i ≫ act 𝒮 Z (fun j => eqToHom (P j) ≫ cell j) m ≫
      eqToHom (j'.symm.trans b) = eqToHom out ≫ act 𝒮 Z raw ws
  rw [h₁, ← Category.assoc, ← Category.assoc, i', ← eqToHom_trans (out.trans a.symm) j,
    Category.assoc]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, j'i, h₃, ← Category.assoc, ai]


end FibreSemantics

section Variation
variable {f : X → Y}
variable (A A' : X → C) (B B' : Y → C)
variable (ps : AddressOrder X xs xs') (pt : AddressOrder Y ys ys')
variable (hx : xs.Nodup) (hy : ys.Nodup)
variable (ha : ∀ x ∈ xs, f x ∈ ys) (hb : ∀ x ∈ xs', f x ∈ ys')
variable (α : ∀ x, A x ≅ A' x) (β : ∀ y, B y ≅ B' y)
variable (p : ∀ y ∈ ys, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A (wordFibre xs f y) ⟶ B y)
variable (q : ∀ y ∈ ys', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A' (wordFibre xs' f y) ⟶ B' y)

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] [DecidableEq Y] in
theorem tagCell_cast {Q R : Y → C} {l : List Y}
    (v : ∀ z ∈ l, Q z ⟶ R z) {t u : Y} (ht : t ∈ l) (hu : u ∈ l) (e : t = u) :
    v t ht ≫ eqToHom (congrArg R e) = eqToHom (congrArg Q e) ≫ v u hu := by
  subst u
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

local notation "Eₛ" => wordEquiv ps.perm hx
local notation "Eₜ" => wordEquiv pt.perm hy

set_option backward.isDefEq.respectTransparency false in
/-- For two actual native word-map arrows the carrier-changing square
is exactly a comparison of the opaque maps on the actual ordered raw
fibres, after the restricted tagged reordering and pointwise shuffle.
The equality for each target tag remains the caller's obligation. -/
theorem wordNativeMap_square_iff :
    let U := wordNativeMap f ha hy A B (fun j => p ys[j] (List.getElem_mem _))
    let V := wordNativeMap f hb (pt.perm.nodup hy) A' B' (fun j => q ys'[j] (List.getElem_mem _))
    U.comp (nativeReindex (A:=wordFamily B ys) (B:=wordFamily B' ys') Eₜ (wordComparisonCells B B' pt hy β)) =
      (nativeReindex (A:=wordFamily A xs) (B:=wordFamily A' xs') Eₛ (wordComparisonCells A A' ps hx α)).comp V ↔
    ∀ j : Fin ys'.length,
      p ys'[j] (pt.perm.mem_iff.mpr (List.getElem_mem _)) ≫ (β ys'[j]).hom =
        AddressOrder.mapSum additiveStructure A (wordFibreOrder f ps ys'[j]) ≫
          act 𝒮 Z (fun x => (α x).hom) (wordFibre xs' f ys'[j]) ≫ q ys'[j] (List.getElem_mem _) := by
  intro U V
  let e := Eₛ
  let d := Eₜ
  let d₁ := wordCarrier f ha hy
  let d₂ := wordCarrier f hb (pt.perm.nodup hy)
  let H : (d : Fin ys.length → Fin ys'.length) ∘ d₁ = d₂ ∘ e :=
    wordCarrier_square ps pt hx hy ha hb
  refine (native_reindex_square_iff U V e d (wordComparisonCells A A' ps hx α)
    (wordComparisonCells B B' pt hy β) H).trans ?_
  constructor <;> intro eq j <;> specialize eq j
  all_goals
    let y := ys'[j]
    let y₀ := ys[d.symm j]
    let E : y₀ = y := wordEquiv_get_symm pt.perm hy j
    let As (i : Fin xs.length) := A xs[i]
    let At (i : Fin xs'.length) := A' xs'[i]
    let g (i : Fin xs.length) := xs[i]
    let l := fibreList (d₂ ∘ e) j
    let m := fibreList d₂ j
    let l' := m.map e.symm
    let F := fun y => fold 𝒮 Z A (wordFibre xs f y)
    let Q₁ := wordFibre xs f y
    let Q₂ := wordFibre xs' f y
    let r := fibreList_preequiv_order e d₂ j
    let α₀ := fun k => (wordComparisonCells A A' ps hx α k).hom
    let a : fibreList (d ∘ d₁) j = fibreList d₁ (d.symm j) := fibreList_postequiv d₁ d j
    let b : standardPushObj d₁ As (d.symm j) = F y₀ := wordCarrier_fibre_pin f ha hy A (d.symm j)
    let c : standardPushObj d₂ At j = fold 𝒮 Z A' Q₂ :=
      wordCarrier_fibre_pin f hb (pt.perm.nodup hy) A' j
    let A₀ : standardPushObj (d ∘ d₁) As j = F y :=
      (congrArg (fold 𝒮 Z As) a).trans (b.trans (congrArg F E))
    let H₀ : standardPushObj (d ∘ d₁) As j = standardPushObj (d₂ ∘ e) As j :=
      congrArg (fun f => standardPushObj f As j) H
    have h₁ : l.map g = Q₁ := by
      have hx : l = fibreList d₁ (d.symm j) := (congrArg (fun v => fibreList v j) H).symm.trans a
      rw [hx, wordCarrier_fibre f ha hy]
      exact congrArg (wordFibre xs f) E
    have h₂ : m.map (fun i => xs'[i]) = Q₂ := wordCarrier_fibre f hb (pt.perm.nodup hy) j
    have h₃ : l'.map g = Q₂ := by
      rw [List.map_map]
      exact (congrArg (fun z => m.map z) (funext (wordEquiv_get_symm ps.perm hx))).trans h₂
    let A₁ : fold 𝒮 Z As l = F y :=
      (std_fold_map A g l).symm.trans (congrArg (fold 𝒮 Z A) h₁)
    let A₂ : fold 𝒮 Z As l' = fold 𝒮 Z A Q₂ :=
      (std_fold_map A g l').symm.trans (congrArg (fold 𝒮 Z A) h₃)
    let A₃ : fold 𝒮 Z As l' = standardPushObj d₂ (fun k => As (e.symm k)) j :=
      std_fold_map As e.symm m
    have q₁ : AddressOrder.mapSum additiveStructure As r ≫ eqToHom A₂ =
        eqToHom A₁ ≫ AddressOrder.mapSum additiveStructure A (wordFibreOrder f ps y) :=
      order_restrict_semantics A g l l' h₁ h₃ (hx.filter _)
        (wordFibreOrder f ps y) r
    have q₂ : eqToHom A₃ ≫ standardPushMap d₂ α₀ j ≫ eqToHom c =
        eqToHom A₂ ≫ act 𝒮 Z (fun x => (α x).hom) Q₂ :=
      wordCells_local_semantics A A' ps hx α m h₂
    have pre : eqToHom H₀ ≫ eqToHom A₁ = eqToHom A₀ := by rw [eqToHom_trans]
    have lc : eqToHom (congrArg (fold 𝒮 Z As) a) ≫ U.cell (d.symm j) ≫
          (wordComparisonCells B B' pt hy β j).hom =
        eqToHom A₀ ≫ p y (pt.perm.mem_iff.mpr (List.getElem_mem _)) ≫ (β y).hom := by
      let F₀ := congrArg F E
      let B₀ := congrArg B E
      have k : p y₀ (List.getElem_mem (l:=ys) _) ≫ eqToHom B₀ =
          eqToHom F₀ ≫ p y (pt.perm.mem_iff.mpr (List.getElem_mem _)) :=
        tagCell_cast p (List.getElem_mem (l:=ys) _) (pt.perm.mem_iff.mpr (List.getElem_mem _)) E
      change eqToHom _ ≫ (eqToHom b ≫ p y₀ _) ≫ (eqToHom B₀ ≫ (β y).hom) = _
      simp only [Category.assoc]
      have comp := congrArg (fun t => eqToHom (congrArg (fold 𝒮 Z As) a) ≫ eqToHom b ≫ t ≫ (β y).hom) k
      simp only [Category.assoc] at comp
      refine comp.trans ?_
      rw [← Category.assoc (eqToHom b), eqToHom_trans,
        ← Category.assoc (eqToHom (congrArg (fold 𝒮 Z As) a)), eqToHom_trans]
    have rc : eqToHom H₀ ≫ AddressOrder.mapSum additiveStructure As r ≫ eqToHom A₃ ≫
          standardPushMap d₂ α₀ j ≫ V.cell j =
        eqToHom A₀ ≫ AddressOrder.mapSum additiveStructure A (wordFibreOrder f ps y) ≫
          act 𝒮 Z (fun x => (α x).hom) Q₂ ≫ q y (List.getElem_mem _) := by
      change _ ≫ _ ≫ _ ≫ _ ≫ (eqToHom c ≫ q y _) = _
      rw [reassoc_of% q₂, ← Category.assoc (AddressOrder.mapSum additiveStructure As r), q₁]
      simp only [Category.assoc]
      rw [← Category.assoc (eqToHom H₀), pre]
    have E₀ : IsIso (eqToHom A₀) := inferInstance
    first
    | exact (cancel_epi (eqToHom A₀)).mp (lc.symm.trans (eq.trans rc))
    | exact lc.trans ((congrArg (fun z => eqToHom A₀ ≫ z) eq).trans rc.symm)

end Variation
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
