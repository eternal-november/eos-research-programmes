module
public import ContextualComposition.NativeDependentIdentity
@[expose] public section

/-! Compose the actual parent and continuation native maps first. This
module decodes their opaque whole-fibre cells into the ordered input
format without factoring them into arrows at individual occurrences. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z t
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

section Decode
variable {X : Type w} {Y : Type z} [DecidableEq Y] {xs : List X} {ys : List Y}
variable (A : X → C) (B : Y → C) (F : X → Y)
variable (hs : ∀ x ∈ xs, F x ∈ ys) (ht : ys.Nodup)

omit [DecidableEq Y] in
theorem wordCarrier_eq_of_get (f : Fin xs.length → Fin ys.length)
    (h : ∀ i : Fin xs.length, ys[f i] = F xs[i]) :
    wordCarrier F hs ht = f := by
  funext i
  exact (wordCarrier_eq_iff F hs ht i (f i)).mpr (h i).symm

set_option backward.isDefEq.respectTransparency false in
def readNativeWordCell (p : Hom ℙ (wordFamily A xs) (wordFamily B ys))
    (h : wordCarrier F hs ht = p.addr) (j : Fin ys.length) :
    fold 𝒮 Zₐ A (wordFibre xs F ys[j]) ⟶ B ys[j] :=
  eqToHom ((wordCarrier_fibre_pin F hs ht A j).symm.trans
    (congrArg (fun f => standardPushObj f (wordFamily A xs).val j) h)) ≫ p.cell j

set_option backward.isDefEq.respectTransparency false in
theorem readNativeWordCell_reassemble (p : Hom ℙ (wordFamily A xs) (wordFamily B ys))
    (h : wordCarrier F hs ht = p.addr) :
    wordNativeMap F hs ht A B (readNativeWordCell A B F hs ht p h) = p := by
  cases p with
  | mk f p =>
    apply native_hom_ext h
    intro i
    let a := wordCarrier_fibre_pin F hs ht A i
    let b := congrArg (fun f => standardPushObj f (wordFamily A xs).val i) h
    change eqToHom a ≫ eqToHom (a.symm.trans b) ≫ p i = eqToHom b ≫ p i
    rw [reassoc_of% eqToHom_trans a (a.symm.trans b)]

noncomputable def decodeNativeWordCell (p : Hom ℙ (wordFamily A xs) (wordFamily B ys))
    (h : wordCarrier F hs ht = p.addr) (y : Y) (hy : y ∈ ys) :
    fold 𝒮 Zₐ A (wordFibre xs F y) ⟶ B y :=
  let j := (wordPositions ys ht).symm ⟨y,hy⟩
  let e : ys[j] = y := congrArg Subtype.val ((wordPositions ys ht).apply_symm_apply ⟨y,hy⟩)
  eqToHom (congrArg (fun x => fold 𝒮 Zₐ A (wordFibre xs F x)) e.symm) ≫
    readNativeWordCell A B F hs ht p h j ≫ eqToHom (congrArg B e)

set_option backward.isDefEq.respectTransparency false in
theorem decodeNativeWordCell_get (p : Hom ℙ (wordFamily A xs) (wordFamily B ys))
    (h : wordCarrier F hs ht = p.addr) (j : Fin ys.length) :
    decodeNativeWordCell A B F hs ht p h ys[j] (List.getElem_mem _) =
      readNativeWordCell A B F hs ht p h j := by
  let k := (wordPositions ys ht).symm ⟨ys[j], List.getElem_mem _⟩
  have H : k = j := (congrArg (wordPositions ys ht).symm
    (show ⟨ys[j], List.getElem_mem _⟩ = wordPositions ys ht j from Subtype.ext rfl)).trans
      ((wordPositions ys ht).symm_apply_apply j)
  have Q {i : Fin ys.length} (e : i = j) :
      eqToHom (congrArg (fun i : Fin ys.length => fold 𝒮 Zₐ A (wordFibre xs F ys[i])) e.symm) ≫
        readNativeWordCell A B F hs ht p h i ≫ eqToHom (congrArg (fun i : Fin ys.length => B ys[i]) e) =
      readNativeWordCell A B F hs ht p h j := by
    subst i
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Q H

set_option backward.isDefEq.respectTransparency false in
theorem decodeNativeWordCell_reassemble (p : Hom ℙ (wordFamily A xs) (wordFamily B ys))
    (h : wordCarrier F hs ht = p.addr) :
    wordNativeMap F hs ht A B (fun j => decodeNativeWordCell A B F hs ht p h ys[j] (List.getElem_mem _)) = p := by
  rw [show (fun j : Fin ys.length => decodeNativeWordCell A B F hs ht p h ys[j] (List.getElem_mem _)) =
    readNativeWordCell A B F hs ht p h from funext (decodeNativeWordCell_get A B F hs ht p h)]
  exact readNativeWordCell_reassemble A B F hs ht p h

end Decode

section Ordered
variable {X U Y V Z W : Type u} [DecidableEq Y] [DecidableEq V] [DecidableEq Z] [DecidableEq W]
variable {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V} {zs : List Z} {ws : Z → List W}
variable {A : X → C} {B : X → U → C} {A' : Y → C} {B' : Y → V → C} {A'' : Z → C} {B'' : Z → W → C}
variable (D : OrderedDependentMap xs us ys vs A B A' B')
variable (E : OrderedDependentMap ys vs zs ws A' B' A'' B'')
variable (hn : ys.Nodup) (hm : zs.Nodup)
variable (hD : ∀ x ∈ xs, (vs (D.parent x)).Nodup)
variable (hE : ∀ y ∈ ys, (ws (E.parent y)).Nodup)

noncomputable def OrderedDependentMap.compose :
    OrderedDependentMap xs us zs ws A B A'' B'' where
  parent := E.parent ∘ D.parent
  child := fun x => E.child (D.parent x) ∘ D.child x
  parent_mem := fun x hx => E.parent_mem _ (D.parent_mem x hx)
  child_mem := fun x hx u hu => E.child_mem _ (D.parent_mem x hx) _ (D.child_mem x hx u hu)
  outer := fun z hz =>
    decodeNativeWordCell A A'' (E.parent ∘ D.parent) (fun x hx => E.parent_mem _ (D.parent_mem x hx)) hm
      ((D.outerNative hn).comp (E.outerNative hm))
      (wordCarrier_comp D.parent E.parent D.parent_mem E.parent_mem hn hm).symm z hz
  inner := fun x hx w hw =>
    let y := D.parent x
    let hy := D.parent_mem x hx
    decodeNativeWordCell (B x) (B'' (E.parent y)) (E.child y ∘ D.child x)
      (fun u hu => E.child_mem y hy _ (D.child_mem x hx u hu)) (hE y hy)
      ((D.innerNative x hx (hD x hx)).comp (E.innerNative y hy (hE y hy)))
      (wordCarrier_comp (D.child x) (E.child y) (D.child_mem x hx) (E.child_mem y hy) (hD x hx) (hE y hy)).symm w hw

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.compose_outer :
    (D.compose E hn hm hD hE).outerNative hm = (D.outerNative hn).comp (E.outerNative hm) := by
  apply decodeNativeWordCell_reassemble

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.compose_inner (x : X) (hx : x ∈ xs) :
    (D.compose E hn hm hD hE).innerNative x hx (hE _ (D.parent_mem x hx)) =
      (D.innerNative x hx (hD x hx)).comp (E.innerNative _ (D.parent_mem x hx) (hE _ (D.parent_mem x hx))) := by
  apply decodeNativeWordCell_reassemble

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.compose_preserves {I : C}
    {α : fold 𝒮 Zₐ A xs ⟶ I} {β : fold 𝒮 Zₐ A' ys ⟶ I} {γ : fold 𝒮 Zₐ A'' zs ⟶ I}
    {δ : ∀ x, fold 𝒮 Zₐ (B x) (us x) ⟶ I}
    {δ' : ∀ y, fold 𝒮 Zₐ (B' y) (vs y) ⟶ I}
    {δ'' : ∀ z, fold 𝒮 Zₐ (B'' z) (ws z) ⟶ I}
    (p : D.Preserves hn hD δ δ' α β) (q : E.Preserves hm hE δ' δ'' β γ) :
    (D.compose E hn hm hD hE).Preserves hm (fun x hx => hE _ (D.parent_mem x hx)) δ δ'' α γ where
  outer := by rw [D.compose_outer, Hom.comp_assoc, q.outer, p.outer]
  inner x hx := by
    rw [D.compose_inner, Hom.comp_assoc]
    exact (congrArg (fun a => (D.innerNative x hx (hD x hx)).comp a)
      (q.inner (D.parent x) (D.parent_mem x hx))).trans (p.inner x hx)

end Ordered

theorem wordCarrier_comp_any {X : Type w} {Y : Type z} {D : Type t}
    {xs : List X} {ys : List Y} {zs : List D}
    (f : X → Y) (g : Y → D) (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hy : ys.Nodup) (hz : zs.Nodup) :
    wordCarrier g hg hz ∘ wordCarrier f hf hy =
      wordCarrier (g ∘ f) (fun x hx => hg _ (hf x hx)) hz := by
  symm
  apply wordCarrier_eq_of_get
  intro i
  exact (wordCarrier_get g hg hz (wordCarrier f hf hy i)).trans (congrArg g (wordCarrier_get f hf hy i))

section RawComposition
variable {X : Type w} {Y : Type z} {D : Type t} [DecidableEq Y] [DecidableEq D]
variable {xs : List X} {ys : List Y} {zs : List D}
variable (A : X → C) (B : Y → C) (D' : D → C) (f : X → Y) (g : Y → D)
variable (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
variable (hy : ys.Nodup) (hz : zs.Nodup)

set_option backward.isDefEq.respectTransparency false in
theorem readCompositeWordCell_raw (hxs : xs.Nodup)
    (p : ∀ j : Fin ys.length, fold 𝒮 Zₐ A (wordFibre xs f ys[j]) ⟶ B ys[j])
    (q : ∀ j : Fin zs.length, fold 𝒮 Zₐ B (wordFibre ys g zs[j]) ⟶ D' zs[j])
    (k : Fin zs.length)
    (r : AddressOrder X (wordFibre xs (g ∘ f) zs[k])
      ((fibreList (wordCarrier g hg hz) k).flatMap (fun j => wordFibre xs f ys[j]))) :
    readNativeWordCell A D' (g ∘ f) (fun x hx => hg _ (hf x hx)) hz
      ((wordNativeMap f hf hy A B p).comp (wordNativeMap g hg hz B D' q))
      (wordCarrier_comp_any f g hf hg hy hz).symm k =
    AddressOrder.mapSum additiveStructure A r ≫
      rowsChart A (fun j => wordFibre xs f ys[j]) (fibreList (wordCarrier g hg hz) k) ≫
      act 𝒮 Zₐ p (fibreList (wordCarrier g hg hz) k) ≫ eqToHom (wordCarrier_fibre_pin g hg hz B k) ≫ q k := by
  let fa := wordCarrier f hf hy
  let ga := wordCarrier g hg hz
  let hab := fun x hx => hg _ (hf x hx)
  let ha := wordCarrier (g ∘ f) hab hz
  let c := wordCarrier_comp_any f g hf hg hy hz
  let a := wordFamily A xs
  let b := wordFamily B ys
  let src := fibreList (ga ∘ fa) k
  let mid := fibreList ga k
  let read := fun i : Fin xs.length => xs[i]
  let F := fold 𝒮 Zₐ A
  let P := fun (j : Fin ys.length) => wordFibre xs f ys[j]
  let S := wordFibre xs (g ∘ f) zs[k]
  let J := standardPushSplit fa ga a.val k
  let K := standardPushMap ga (fun j => eqToHom (wordCarrier_fibre_pin f hf hy A j) ≫ p j) k
  let pin := wordCarrier_fibre_pin g hg hz B k
  let e : src.map read = S := (congrArg (fun u => (fibreList u k).map read) c).trans
    (wordCarrier_fibre (g ∘ f) hab hz k)
  let r₀ := splitOrder fa ga k
  let rr := (r₀.relabel read).seq (castOrder
    ((List.map_flatMap (f:=read) (g:=fibreList fa) (l:=mid)).trans
      (congrArg (fun Q => mid.flatMap Q) (funext (wordCarrier_fibre f hf hy)))))
  let rr' := (castOrder e.symm).seq rr
  have m := wordChart_retag A b.val read src (fibreList fa) P mid (wordCarrier_fibre f hf hy) r₀ p
  dsimp only at m
  have w : J ≫ K = eqToHom (std_fold_map A read src).symm ≫
      AddressOrder.mapSum additiveStructure A rr ≫ rowsChart A P mid ≫ act 𝒮 Zₐ p mid := by
    simp only [J, K, standardPushSplit, standardPushMap, Category.assoc]
    exact m
  let tr := (wordCarrier_fibre_pin (g ∘ f) hab hz A k).symm.trans
    (congrArg (fun u => standardPushObj u a.val k) c.symm)
  change eqToHom tr ≫ (J ≫ K ≫ eqToHom pin ≫ q k) = _
  rw [show J ≫ K ≫ eqToHom pin ≫ q k = (J ≫ K) ≫ eqToHom pin ≫ q k from (Category.assoc _ _ _).symm, w]
  simp only [Category.assoc]
  have H : AddressOrder.mapSum additiveStructure A r =
      eqToHom (congrArg F e.symm) ≫ AddressOrder.mapSum additiveStructure A rr := by
    have u := tagged_permutation_coherent A (hxs.filter _) r rr'
    change AddressOrder.mapSum additiveStructure A r =
      AddressOrder.mapSum additiveStructure A (castOrder e.symm) ≫ AddressOrder.mapSum additiveStructure A rr at u
    rw [castOrder_map] at u
    exact u
  rw [H]
  simp only [Category.assoc]
  rw [reassoc_of% eqToHom_trans tr (std_fold_map A read src).symm]

end RawComposition
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
