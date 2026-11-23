module
public import ContextualComposition.NativeDependentCompositionExchange
@[expose] public section

/-! Retag a chosen grid only on its actual supported leaves. This avoids
a fictitious default address when the ambient target is empty. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X : Type w} {Y : Type z}

def supportedRetagGrid (P : X → Prop) (f : {x // P x} → Y) :
    (e : GridExpr X) → (∀ x ∈ e.leaves, P x) → GridExpr Y
  | .zero, _ => .zero
  | .leaf x, h => .leaf (f ⟨x, h x List.mem_cons_self⟩)
  | .bin a b, h =>
      .bin (supportedRetagGrid P f a (fun x hx => h x (List.mem_append_left _ hx)))
        (supportedRetagGrid P f b (fun x hx => h x (List.mem_append_right _ hx)))

set_option backward.isDefEq.respectTransparency false in
theorem supportedRetagGrid_leaves (P : X → Prop) (f : {x // P x} → Y)
    (e : GridExpr X) (h : ∀ x ∈ e.leaves, P x) :
    (supportedRetagGrid P f e h).leaves = e.leaves.pmap (fun x hx => f ⟨x,hx⟩) h := by
  induction e with
  | zero => rfl
  | leaf x => rfl
  | bin a b ha hb =>
    change (supportedRetagGrid P f a _).leaves ++ (supportedRetagGrid P f b _).leaves =
      (a.leaves ++ b.leaves).pmap (fun x hx => f ⟨x,hx⟩) h
    rw [ha, hb, List.pmap_append]

theorem supportedRetagGrid_plain (P : X → Prop) (f : {x // P x} → Y) (g : X → Y)
    (e : GridExpr X) (h : ∀ x ∈ e.leaves, P x) (hf : ∀ x (hx : P x), f ⟨x,hx⟩ = g x) :
    supportedRetagGrid P f e h = retagGrid g e := by
  induction e with
  | zero => rfl
  | leaf x => exact congrArg GridExpr.leaf (hf x _)
  | bin a b ha hb =>
    exact congrArg₂ GridExpr.bin (ha (fun x hx => h x (List.mem_append_left _ hx)))
      (hb (fun x hx => h x (List.mem_append_right _ hx)))

theorem retagGrid_supportedRetag {Z : Type*} (P : X → Prop) (f : {x // P x} → Y) (g : Y → Z)
    (e : GridExpr X) (h : ∀ x ∈ e.leaves, P x) :
    retagGrid g (supportedRetagGrid P f e h) = supportedRetagGrid P (g ∘ f) e h := by
  induction e with
  | zero => rfl
  | leaf x => rfl
  | bin a b ha hb =>
    exact congrArg₂ GridExpr.bin (ha (fun x hx => h x (List.mem_append_left _ hx)))
      (hb (fun x hx => h x (List.mem_append_right _ hx)))

/-- The admissible supports may be empty; no inhabitant of the word or
either address type is ever selected. -/
theorem supportedRetagGrid_zero (P : X → Prop) (f : {x // P x} → Y) :
    supportedRetagGrid P f .zero (fun _ h => False.elim (List.not_mem_nil h)) = .zero := rfl


section Dependent
variable {P U P' U' : Type u}
variable [DecidableEq P'] [DecidableEq U']
variable {ps : List P} {us : P → List U} {ps' : List P'} {us' : P' → List U'}
variable {V : P → C} {W : P → U → C} {V' : P' → C} {W' : P' → U' → C}
variable (D : OrderedDependentMap ps us ps' us' V W V' W')
variable {T : Bi (coeff (C:=C))}

def dependentFibreLocalTree (t : P' × U') : GridExpr (D.Slice t.1 × U) :=
  dependentExpr (D.slice t.1) (D.terms t.1 t.2)

def dependentFibreRawTree (t : P' × U') : GridExpr (P × U) :=
  retagGrid (dependentSliceRelabel D t.1) (dependentFibreLocalTree D t)

theorem dependentFibreRawTree_leaves (t : P' × U') :
    (dependentFibreRawTree D t).leaves = wordFibre (dependentWord ps us) (origDepCarrier D) t :=
  (retagGrid_leaves _ _).trans (dependentSlice_word D t)

variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

def dependentFibreRawCell (t : P' × U') (ht : t ∈ dependentWord ps' us') :
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (dependentLabels (T:=T) V W) (dependentFibreRawTree D t) ⟶
      dependentLabels (T:=T) V' W' t :=
  let h := (dependentWord_mem ps' us' t).mp ht
  eqToHom (retagGrid_eval (dependentLabels (T:=T) V W) (dependentSliceRelabel D t.1)
    (dependentFibreLocalTree D t)) ≫
  eqToHom (dependentExpr_eval (T:=T) (D.parentVal t.1) (D.childVal t.1) (D.slice t.1) (D.terms t.1 t.2)) ≫
  dep R (D.parentVal t.1) (indexInput (D.childVal t.1) (D.terms t.1 t.2)) L
    (D.slice t.1) (D.locInner t.1 t.2 h.2) (D.locOuter t.1 h.1)

set_option backward.isDefEq.respectTransparency false in
theorem dependentFibreRawCell_assemble (t : P' × U') (ht : t ∈ dependentWord ps' us') :
    eqToHom (congrArg (fold 𝒮 Zₐ (dependentLabels (T:=T) V W)) (dependentFibreRawTree_leaves D t).symm) ≫
      compressGrid (dependentLabels (T:=T) V W) (dependentFibreRawTree D t) ≫
      dependentFibreRawCell D R L t ht = origDependentCell D R L t ht := by
  let A := dependentLabels (T:=T) V W
  let G := fold 𝒮 Zₐ A
  let f := dependentSliceRelabel D t.1
  let e := dependentFibreLocalTree D t
  let h := retagGrid_leaves f e
  let d := dependentSlice_word D t
  have q := compressGrid_retag A f e
  unfold dependentFibreRawCell origDependentCell localCellToGlobal
  change eqToHom (congrArg G (h.trans d).symm) ≫ compressGrid A (retagGrid f e) ≫
      eqToHom (retagGrid_eval A f e) ≫ _ = _
  rw [reassoc_of% q, reassoc_of% eqToHom_trans]
  rfl

theorem dependentFibreLocalSupport (t : P' × U') (p : D.Slice t.1 × U)
    (h : p ∈ (dependentFibreLocalTree D t).leaves) :
    dependentSliceRelabel D t.1 p ∈ dependentWord ps us := by
  have H : dependentSliceRelabel D t.1 p ∈ (dependentFibreLocalTree D t).leaves.map (dependentSliceRelabel D t.1) := List.mem_map.mpr ⟨p,h,rfl⟩
  rw [dependentFibreLocalTree, dependentSlice_word D t] at H
  exact (List.mem_filter.mp H).1

noncomputable def dependentFibreIndexTree (h : (dependentWord ps us).Nodup) (t : P' × U') :
    GridExpr (Fin (dependentWord ps us).length) :=
  supportedRetagGrid (fun p => dependentSliceRelabel D t.1 p ∈ dependentWord ps us)
    (fun p => (wordPositions (dependentWord ps us) h).symm ⟨dependentSliceRelabel D t.1 p.val,p.property⟩)
    (dependentFibreLocalTree D t) (dependentFibreLocalSupport D t)

theorem dependentFibreIndex_decode (h : (dependentWord ps us).Nodup) (t : P' × U') :
    retagGrid (fun i : Fin (dependentWord ps us).length => (dependentWord ps us)[i])
      (dependentFibreIndexTree D h t) = dependentFibreRawTree D t := by
  unfold dependentFibreIndexTree dependentFibreRawTree
  rw [retagGrid_supportedRetag]
  apply supportedRetagGrid_plain
  intro p hP
  exact congrArg Subtype.val ((wordPositions (dependentWord ps us) h).apply_symm_apply ⟨_,hP⟩)

set_option backward.isDefEq.respectTransparency false in
theorem dependentFibreIndex_leaves (h : (dependentWord ps us).Nodup) (h' : (dependentWord ps' us').Nodup)
    (j : Fin (dependentWord ps' us').length) :
    let _s := dependentWord ps us
    let t := (dependentWord ps' us')[j]
    (dependentFibreIndexTree D h t).leaves =
      fibreList (wordCarrier (origDepCarrier D) (origDepCarrier_support D) h') j := by
  intro s t
  let f := fun i : Fin s.length => s[i]
  let e := dependentFibreIndexTree D h t
  have hf : Function.Injective f := by
    intro i j hh
    exact Fin.ext (h.getElem_inj.mp hh)
  have H : e.leaves.map f =
      (fibreList (wordCarrier (origDepCarrier D) (origDepCarrier_support D) h') j).map f := by
    rw [← retagGrid_leaves, dependentFibreIndex_decode, dependentFibreRawTree_leaves]
    exact (wordCarrier_fibre (origDepCarrier D) (origDepCarrier_support D) h' j).symm
  exact (List.map_inj_right (f:=f) (fun _ _ e => hf e)).mp H


theorem dependentFibreIndex_eval (h : (dependentWord ps us).Nodup) (t : P' × U') :
    let A := dependentLabels (T:=T) V W
    let s := dependentWord ps us
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun i : Fin s.length => A s[i]) (dependentFibreIndexTree D h t) =
      GridExpr.eval (S:=𝒮) (Z:=Zₐ) A (dependentFibreRawTree D t) := by
  intro A s
  let f := fun i : Fin s.length => s[i]
  let e := dependentFibreIndexTree D h t
  exact (retagGrid_eval A f e).symm.trans
    (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) A) (dependentFibreIndex_decode D h t))

noncomputable def dependentFibreIndexCell (h : (dependentWord ps us).Nodup) (t : P' × U') (ht : t ∈ dependentWord ps' us') :
    let A := dependentLabels (T:=T) V W
    let s := dependentWord ps us
    GridExpr.eval (S:=𝒮) (Z:=Zₐ) (fun i : Fin s.length => A s[i]) (dependentFibreIndexTree D h t) ⟶
      dependentLabels (T:=T) V' W' t :=
  eqToHom (dependentFibreIndex_eval D h t) ≫ dependentFibreRawCell D R L t ht

set_option backward.isDefEq.respectTransparency false in
theorem dependentFibreIndexCell_assemble
    (h : (dependentWord ps us).Nodup) (h' : (dependentWord ps' us').Nodup)
    (j : Fin (dependentWord ps' us').length) :
    let t := (dependentWord ps' us')[j]
    let A := dependentLabels (T:=T) V W
    let xs := dependentWord ps us
    let A₀ := fun i : Fin xs.length => A xs[i]
    let d := dependentFibreIndex_leaves D h h' j
    let out := wordCarrier_fibre_pin (origDepCarrier D) (origDepCarrier_support D) h' A j
    compressGrid A₀ (dependentFibreIndexTree D h t) ≫ dependentFibreIndexCell D R L h t (List.getElem_mem _) =
      eqToHom (congrArg (fold 𝒮 Zₐ A₀) d) ≫ eqToHom out ≫ origDependentCell D R L t (List.getElem_mem _) := by
  intro t A xs A₀ d out
  let f := fun i : Fin xs.length => xs[i]
  let s := dependentFibreIndexTree D h t
  let r := dependentFibreRawTree D t
  let z := dependentFibreIndex_decode D h t
  let a := retagGrid_eval A f s
  let b := (congrArg (fold 𝒮 Zₐ A) (retagGrid_leaves f s)).trans (std_fold_map A f s.leaves)
  let c := congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) A) z
  let y := dependentFibreRawCell D R L t (List.getElem_mem _)
  let e := congrArg (fold 𝒮 Zₐ A) (dependentFibreRawTree_leaves D t).symm
  have H := compressGrid_retag A f s
  have j : compressGrid A r =
      eqToHom (congrArg (fun t => fold 𝒮 Zₐ A t.leaves) z.symm) ≫
        compressGrid A (retagGrid f s) ≫ eqToHom c := by
    have aux {r s : GridExpr _} (z : r = s) :
        compressGrid A s = eqToHom (congrArg (fun t => fold 𝒮 Zₐ A t.leaves) z.symm) ≫
          compressGrid A r ≫ eqToHom (congrArg (GridExpr.eval (S:=𝒮) (Z:=Zₐ) A) z) := by
      cases z
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact aux z
  have H' : compressGrid A₀ s ≫ eqToHom a.symm = eqToHom b.symm ≫ compressGrid A (retagGrid f s) := by
    have K := congrArg (fun w => eqToHom b.symm ≫ w ≫ eqToHom a.symm) H
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Category.id_comp] at K
    exact K.symm
  have hF := dependentFibreRawCell_assemble D R L t (List.getElem_mem _)
  change compressGrid A₀ s ≫ (eqToHom (a.symm.trans c) ≫ y) =
    eqToHom (congrArg (fold 𝒮 Zₐ A₀) d) ≫ eqToHom out ≫ origDependentCell D R L t (List.getElem_mem _)
  rw [← eqToHom_trans a.symm c]
  simp only [Category.assoc]
  rw [reassoc_of% H', ← hF, j]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

end Dependent

section Sequential
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

noncomputable def sequentialDependentFibreTree (h : (dependentWord ys vs).Nodup) (t : Z × W) :
    GridExpr (X × U) :=
  graftGrid (fun j : Fin (dependentWord ys vs).length => dependentFibreRawTree D (dependentWord ys vs)[j])
    (dependentFibreIndexTree E h t)

noncomputable def sequentialDependentFibreOrder (h : (dependentWord ys vs).Nodup)
    (h' : (dependentWord zs ws).Nodup) (k : Fin (dependentWord zs ws).length) :
    AddressOrder (X × U)
      (wordFibre (dependentWord xs us) (origDepCarrier E ∘ origDepCarrier D) (dependentWord zs ws)[k])
      (sequentialDependentFibreTree D E h (dependentWord zs ws)[k]).leaves := by
  let xs₀ := dependentWord xs us
  let ys₀ := dependentWord ys vs
  let zs₀ := dependentWord zs ws
  let f := origDepCarrier D
  let g := origDepCarrier E
  let p := origDepCarrier_support D
  let q := origDepCarrier_support E
  let D₀ := wordCarrier f p h
  let E₀ := wordCarrier g q h'
  let e := dependentFibreIndexTree E h zs₀[k]
  let P := fun j : Fin ys₀.length => dependentFibreRawTree D ys₀[j]
  let fd := fun j : Fin xs₀.length => xs₀[j]
  let rr := splitOrder D₀ E₀ k
  have o₀ : (fibreList (E₀ ∘ D₀) k).map fd = wordFibre xs₀ (g ∘ f) zs₀[k] :=
    (congrArg (fun d => (fibreList d k).map fd) (wordCarrier_comp f g p q h h')).trans
      (wordCarrier_fibre (g ∘ f) (fun _ hz => q _ (p _ hz)) h' k)
  let s := fibreList E₀ k
  have o₁ : (s.flatMap (fibreList D₀)).map fd = (graftGrid P e).leaves := by
    rw [List.map_flatMap, graftGrid_leaves, dependentFibreIndex_leaves E h h' k]
    exact congrArg (fun M => s.flatMap M)
      (funext fun j => (wordCarrier_fibre f p h j).trans (dependentFibreRawTree_leaves D ys₀[j]).symm)
  exact (castOrder o₀.symm).seq ((rr.relabel fd).seq (castOrder o₁))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The actual composite of the two original dependent arrows has exactly
the grafted chart coefficient, using both original opaque input stages.
This theorem identifies the sequential side; the one-step route still
requires the dependent composition comparison. -/
theorem sequentialDependentFibre_read
    (h₀ : (dependentWord xs us).Nodup) (h : (dependentWord ys vs).Nodup)
    (h' : (dependentWord zs ws).Nodup) (k : Fin (dependentWord zs ws).length) :
    let yw := dependentWord ys vs
    let zw := dependentWord zs ws
    let t := zw[k]
    let G₀ := dependentLabels (T:=T) A B
    let G₂ := dependentLabels (T:=T) A'' B''
    let e := dependentFibreIndexTree E h t
    let P := fun j : Fin yw.length => dependentFibreRawTree D yw[j]
    let p := fun j : Fin yw.length => dependentFibreRawCell D R L yw[j] (List.getElem_mem _)
    let q := dependentFibreIndexCell E R L h t (List.getElem_mem _)
    let supp := fun x hx => origDepCarrier_support E _ (origDepCarrier_support D x hx)
    let eq := (wordCarrier_comp (origDepCarrier D) (origDepCarrier E) (origDepCarrier_support D)
      (origDepCarrier_support E) h h').symm
    readNativeWordCell G₀ G₂ (origDepCarrier E ∘ origDepCarrier D) supp h'
      ((origDependentWordMap D R L h).comp (origDependentWordMap E R L h')) eq k =
    AddressOrder.mapSum additiveStructure G₀ (sequentialDependentFibreOrder D E h h' k) ≫
      compressGrid G₀ (graftGrid P e) ≫ eqToHom (graftGrid_eval G₀ P e) ≫
      GridExpr.actE (S:=𝒮) (Z:=Zₐ) p e ≫ q := by
  intro yw zw t G₀ G₂ e P p q supp eq
  let G₁ := dependentLabels (T:=T) A' B'
  let L₀ := fun j : Fin yw.length => dependentFibreRawTree_leaves D yw[j]
  let pp := fun j : Fin yw.length => eqToHom (congrArg (fold 𝒮 Zₐ G₀) (L₀ j).symm) ≫
    compressGrid G₀ (P j) ≫ p j
  let pp' := fun j : Fin yw.length => origDependentCell D R L yw[j] (List.getElem_mem _)
  let qq := fun j : Fin zw.length => origDependentCell E R L zw[j] (List.getElem_mem _)
  have hP : pp = pp' := funext fun j => dependentFibreRawCell_assemble D R L yw[j] (List.getElem_mem _)
  have H := readCompositeWordCell_grafted G₀ G₁ G₂ (origDepCarrier D) (origDepCarrier E)
    (origDepCarrier_support D) (origDepCarrier_support E) h₀ h h' k P e
    (dependentFibreIndex_leaves E h h' k) L₀ p qq (sequentialDependentFibreOrder D E h h' k) q
    (dependentFibreIndexCell_assemble E R L h h' k)
  change readNativeWordCell G₀ G₂ (origDepCarrier E ∘ origDepCarrier D) supp h'
    ((wordNativeMap (origDepCarrier D) (origDepCarrier_support D) h G₀ G₁ pp).comp
      (wordNativeMap (origDepCarrier E) (origDepCarrier_support E) h' G₁ G₂ qq)) eq k = _ at H
  rw [hP] at H
  exact H

end Sequential
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
