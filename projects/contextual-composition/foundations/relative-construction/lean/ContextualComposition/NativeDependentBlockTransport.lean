module
public import ContextualComposition.NativeDependentFlatten
@[expose] public section
/-! The selected parent words are the literal blocks of the whole native
dependent arrow, with independent source and target tag embeddings. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X U X' U' : Type u} [DecidableEq X'] [DecidableEq U']
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
variable {T : Bi (coeff (C:=C))}

theorem wordFibre_parent {X U Y : Type u} [DecidableEq Y] (f : X → Y)
    (xs : List X) (us : X → List U) (y : Y) :
    wordFibre (dependentWord xs us) (f ∘ Prod.fst) y =
      dependentWord (parentFibreA xs f y) us := by
  simp only [wordFibre, dependentWord, parentFibreA, List.filter_flatMap, List.filter_map, flatMap_filter_if]
  congr 1
  funext x
  by_cases h : f x = y
  · have e : (us x).filter (fun _ => true) = us x := List.filter_eq_self.mpr (fun _ _ => rfl)
    simpa only [Function.comp_def, h, decide_true, ite_true] using congrArg (fun l => l.map (fun u => (x,u))) e
  · have e : (us x).filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (fun _ _ => by decide)
    simpa only [Function.comp_def, h, decide_false, Bool.false_eq_true, ite_false, List.map_nil] using
      congrArg (fun l => l.map (fun u => (x,u))) e

theorem selectedBlockWord_map (a : X') :
    (selectedBlockWord D a).map (dependentSliceRelabel D a) =
      wordFibre (dependentWord xs us) (D.parent ∘ Prod.fst) a := by
  rw [wordFibre_parent]
  change (dependentWord (D.slice a) (us ∘ Subtype.val)).map (fun p => (p.1.val,p.2)) = _
  rw [dependentWord_relabel, sliceWord_map]

private theorem filtered_singleton_of_nodup {X : Type u} [DecidableEq X] {xs : List X}
    (n : xs.Nodup) {x : X} (h : x ∈ xs) :
    parentFibreA xs id x = [x] := by
  unfold parentFibreA
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    by_cases e : a = x
    · subst a
      have hh := (List.nodup_cons.mp n).1
      have k : xs.filter (fun b => decide (id b = x)) = [] :=
        List.filter_eq_nil_iff.mpr (fun b hb => by
          intro e
          have z : b = x := of_decide_eq_true e
          exact hh (z ▸ hb))
      simp only [List.filter_cons, id_eq, decide_true, ite_true] at *
      exact congrArg (List.cons x) k
    · have hh : x ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      simpa only [List.filter_cons, id_eq, e, decide_false, Bool.false_eq_true, ite_false] using ih (List.nodup_cons.mp n).2 hh

omit [DecidableEq U'] in
theorem targetParentBlockWord (n : xs'.Nodup) {a : X'} (ha : a ∈ xs') :
    wordFibre (dependentWord xs' us') (Prod.fst : X' × U' → X') a = (us' a).map (fun t => (a,t)) := by
  change wordFibre (dependentWord xs' us') (id ∘ Prod.fst) a = _
  rw [wordFibre_parent, filtered_singleton_of_nodup n ha]
  simp only [dependentWord, List.flatMap_cons, List.flatMap_nil, List.append_nil]

omit [DecidableEq X'] [DecidableEq U'] in
theorem outerBlock_support : ∀ t ∈ dependentWord xs' us', (Prod.fst : X' × U' → X') t ∈ xs' :=
  fun t ht => ((dependentWord_mem xs' us' t).mp ht).1

set_option backward.isDefEq.respectTransparency false in
theorem origDependent_block_source_word (h : (dependentWord xs' us').Nodup) (hn : xs'.Nodup)
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (j : Fin xs'.length) :
    let P := origDependentWordMap D R L h
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    (fibreList (sel ∘ P.addr) j).map (fun i => (dependentWord xs us)[i]) =
      (selectedBlockWord D a).map (dependentSliceRelabel D a) := by
  intro P sel a
  exact (wordCarrier_block_fibre (origDepCarrier D) Prod.fst (origDepCarrier_support D)
    (outerBlock_support (us':=us')) h hn j).trans (selectedBlockWord_map D a).symm

omit [DecidableEq U'] in
theorem origDependent_block_target_word (hn : xs'.Nodup) (j : Fin xs'.length) :
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    (fibreList sel j).map (fun i => (dependentWord xs' us')[i]) = (us' a).map (fun t => (a,t)) := by
  intro sel a
  exact (wordCarrier_fibre Prod.fst (outerBlock_support (us':=us')) hn j).trans
    (targetParentBlockWord (us':=us') hn (List.getElem_mem _))

theorem origDependent_block_fibre_map {a : X'} (t : U') :
    (wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t).map (dependentSliceRelabel D a) =
      wordFibre (dependentWord xs us) (origDepCarrier D) (a,t) := by
  rw [← selectedChildColumn_leaves D a t]
  exact dependentSlice_word D (a,t)

set_option backward.isDefEq.respectTransparency false in
theorem origDependent_block_cell (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {a : X'} (ha : a ∈ xs') (t : U') (ht : t ∈ us' a) :
    let A := dependentLabels (T:=T) V W
    let g := dependentSliceRelabel D a
    let w := wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t
    let e := origDependent_block_fibre_map D t (a:=a)
    origDependentCell D R L (a,t) ((dependentWord_mem xs' us' _).mpr ⟨ha,ht⟩) =
      eqToHom ((congrArg (fold 𝒮 Zₐ A) e.symm).trans (std_fold_map A g w)) ≫
        selectedChildBlockCell D R L a ha t ht := by
  intro A g w e
  rw [origDependentCell_column]
  unfold localCellToGlobal selectedChildBlockCell
  rw [← Category.assoc (eqToHom ((congrArg (fold 𝒮 Zₐ A) e.symm).trans (std_fold_map A g w))),
    eqToHom_trans]
  rfl

omit [DecidableEq U'] in
theorem origDependent_block_target_length (hn : xs'.Nodup) (j : Fin xs'.length) :
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    (fibreList sel j).length = (us' xs'[j]).length := by
  intro sel
  have h := congrArg List.length (origDependent_block_target_word (us':=us') hn j)
  simpa only [List.length_map] using h

omit [DecidableEq U'] in
theorem origDependent_block_target_read (hn : xs'.Nodup) (j : Fin xs'.length) :
    let sel := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let b := fibreList sel j
    let a := xs'[j]
    let e := origDependent_block_target_length (us':=us') hn j
    ∀ i : Fin b.length, (dependentWord xs' us')[b[i]] = (a, (us' a)[Fin.cast e i]) := by
  intro sel b a e i
  let k := i.val
  let p := fun x : Fin (dependentWord xs' us').length => (dependentWord xs' us')[x]
  have h : b.map p = (us' a).map (fun t => (a,t)) := origDependent_block_target_word (us':=us') hn j
  have z := congrArg (fun l => l[k]?) h
  have h₁ : k < (b.map p).length := by simpa only [List.length_map] using i.isLt
  have h₂ : k < ((us' a).map (fun t => (a,t))).length := by
    rw [List.length_map]
    exact (Fin.cast e i).isLt
  rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂, Option.some.injEq] at z
  simp only [List.getElem_map] at z
  exact z

set_option backward.isDefEq.respectTransparency false in
theorem restrictedDependent_fibre_read
    (h : (dependentWord xs' us').Nodup) (hn : xs'.Nodup)
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (j : Fin xs'.length) :
    let P := origDependentWordMap D R L h
    let s := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    let x := fibreList (s ∘ P.addr) j
    let y := fibreList s j
    let f := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
    let e := origDependent_block_target_length (us':=us') hn j
    ∀ i : Fin y.length,
      (wordFibre x P.addr y[i]).map f =
        (wordFibre (selectedBlockWord D a) (selectedChildAddr D a) (us' a)[Fin.cast e i]).map
          (dependentSliceRelabel D a) := by
  intro P s a x y f e i
  have hh := restricted_fibre P.addr s j (List.getElem_mem (l:=y) (n:=i.val) i.isLt)
  have hm := wordCarrier_fibre (origDepCarrier D) (origDepCarrier_support D) h y[i]
  refine (congrArg (fun q => q.map f) hh).trans ?_
  exact hm.trans ((congrArg (wordFibre (dependentWord xs us) (origDepCarrier D))
    (origDependent_block_target_read (us':=us') hn j i)).trans
      (origDependent_block_fibre_map D (us' a)[Fin.cast e i] (a:=a)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Exact original restricted coefficient read into its untransported
selected parent block cell. Both the source order pin and the target
coefficient pin are literal equalities of the retained addresses. -/
theorem restrictedDependent_cell_read
    (h : (dependentWord xs' us').Nodup) (hn : xs'.Nodup)
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (j : Fin xs'.length) :
    let P := origDependentWordMap D R L h
    let s := wordCarrier Prod.fst (outerBlock_support (us':=us')) hn
    let a := xs'[j]
    let x := fibreList (s ∘ P.addr) j
    let y := fibreList s j
    let f := fun k : Fin (dependentWord xs us).length => (dependentWord xs us)[k]
    let e := origDependent_block_target_length (us':=us') hn j
    let A := dependentLabels (T:=T) V W
    let A' := dependentLabels (T:=T) V' W'
    ∀ i : Fin y.length,
      let t := (us' a)[Fin.cast e i]
      let U := wordFibre x P.addr y[i]
      let Q := wordFibre (selectedBlockWord D a) (selectedChildAddr D a) t
      let g := dependentSliceRelabel D a
      let z := restrictedDependent_fibre_read D h hn R L j i
      let k := origDependent_block_target_read (us':=us') hn j i
      eqToHom (congrArg (fold 𝒮 Zₐ (wordFamily A (dependentWord xs us)).val)
        (restricted_fibre P.addr s j (List.getElem_mem _))) ≫ P.cell y[i] =
      eqToHom (((std_fold_map A f U).symm.trans (congrArg (fold 𝒮 Zₐ A) z)).trans (std_fold_map A g Q)) ≫
        selectedChildBlockCell D R L a (List.getElem_mem _) t (List.getElem_mem _) ≫ eqToHom (congrArg A' k.symm) := by
  intro P s a x y f e A A' i t U Q g z k
  let F := fold 𝒮 Zₐ A
  let path := origDependent_block_fibre_map D t (a:=a)
  let ip := wordCarrier_fibre_pin (origDepCarrier D) (origDepCarrier_support D) h A y[i]
  let b := (dependentWord xs' us')[y[i]]
  let hp : b ∈ dependentWord xs' us' := List.getElem_mem _
  let ha : a ∈ xs' := List.getElem_mem _
  let ht : t ∈ us' a := List.getElem_mem _
  let q := selectedChildBlockCell D R L a ha t ht
  have H (r r' : X' × U') (u : r = r') (hv : r ∈ dependentWord xs' us') (hv' : r' ∈ dependentWord xs' us') :
      origDependentCell D R L r hv ≫ eqToHom (congrArg A' u) =
        eqToHom (congrArg F (congrArg (wordFibre (dependentWord xs us) (origDepCarrier D)) u)) ≫
          origDependentCell D R L r' hv' := by
    cases u
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  have H' := H (a,t) b k.symm ((dependentWord_mem xs' us' _).mpr ⟨ha,ht⟩) hp
  have B := origDependent_block_cell D R L ha t ht
  dsimp only at B
  let d := congrArg (fold 𝒮 Zₐ (wordFamily A (dependentWord xs us)).val) (restricted_fibre P.addr s j (List.getElem_mem (l:=y) (n:=i.val) i.isLt))
  let k₁ := congrArg F (congrArg (wordFibre (dependentWord xs us) (origDepCarrier D)) k.symm)
  let k₂ := congrArg F path.symm
  have B' : origDependentCell D R L b hp =
      eqToHom k₁.symm ≫ (eqToHom (k₂.trans (std_fold_map A g Q)) ≫ q) ≫ eqToHom (congrArg A' k.symm) := by
    let z₀ := eqToHom k₁
    let _ : IsIso z₀ := inferInstanceAs (IsIso (eqToHom k₁))
    apply (cancel_epi z₀).mp
    have hcan : eqToHom k₁ ≫ eqToHom k₁.symm = 𝟙 _ := by rw [eqToHom_trans]; rfl
    change z₀ ≫ origDependentCell D R L b hp =
      eqToHom k₁ ≫ eqToHom k₁.symm ≫ (eqToHom (k₂.trans (std_fold_map A g Q)) ≫ q) ≫ eqToHom (congrArg A' k.symm)
    rw [reassoc_of% hcan, ← B]
    exact H'.symm
  change eqToHom d ≫ (eqToHom ip ≫ origDependentCell D R L b hp) = _
  rw [B']
  simp only [Category.assoc]
  rw [reassoc_of% eqToHom_trans d ip, reassoc_of% eqToHom_trans (d.trans ip) k₁.symm,
    reassoc_of% eqToHom_trans ((d.trans ip).trans k₁.symm) (k₂.trans (std_fold_map A g Q))]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
