module
public import ContextualComposition.NativeDependentPairFunctoriality
public import ContextualComposition.NativeDependentOrderWhisker
@[expose] public section

/-! Additive presentation changes retain raw names and whole-fibre cells. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

noncomputable def orderSumIso {W : Type u} (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) : fold 𝒮 Zₐ A xs ≅ fold 𝒮 Zₐ A ys :=
  let v := AddressOrder.mapSumInv (A:=A) SumTree.stdAddInvertible p
  ⟨AddressOrder.mapSum additiveStructure A p, v.inv, v.hi, v.ih⟩

variable {I : C}

noncomputable def OrderedDependentAugData.reorder (D : OrderedDependentAugData I)
    {xs : List D.X} {us : D.X → List D.U}
    (e : AddressOrder D.X D.xs xs) (d : ∀ x, AddressOrder D.U (D.us x) (us x)) :
    OrderedDependentAugData I where
  X := D.X
  U := D.U
  eqX := D.eqX
  eqU := D.eqU
  xs := xs
  us := us
  V := D.V
  A := D.A
  xs_unique := e.perm.nodup D.xs_unique
  us_unique x hx := (d x).perm.nodup (D.us_unique x (e.perm.mem_iff.mpr hx))
  ε := (orderSumIso D.V e).inv ≫ D.ε
  δ x := (orderSumIso (D.A x) (d x)).inv ≫ D.δ x

set_option backward.isDefEq.respectTransparency false in
theorem wordReorder_preserves {W : Type u} (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) (hx : xs.Nodup) (ε : fold 𝒮 Zₐ A xs ⟶ I) :
    (wordReorderIso A p hx).hom.comp (wordAug A ys ((orderSumIso A p).inv ≫ ε)).ε =
      (wordAug A xs ε).ε := by
  apply wordAug_preserving A A p hx (fun w => Iso.refl (A w))
  change (orderSumIso A p).hom ≫ act 𝒮 Zₐ (fun x => 𝟙 (A x)) ys ≫ (orderSumIso A p).inv ≫ ε = ε
  have h : act 𝒮 Zₐ (fun x => 𝟙 (A x)) ys = 𝟙 _ := occurrence_act_id A ys
  rw [h, Category.id_comp, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem wordReorder_carrier {W : Type u} [DecidableEq W] (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) (hx : xs.Nodup) :
    wordCarrier id (fun _ h => p.perm.mem_iff.mp h) (p.perm.nodup hx) =
      (wordReorderIso A p hx).hom.addr := by
  apply wordCarrier_eq_of_get
  exact wordEquiv_get p.perm hx

set_option backward.isDefEq.respectTransparency false in
theorem wordReorder_cell_heq {W : Type u} (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) (hx : xs.Nodup) (j : Fin ys.length) :
    HEq ((wordReorderIso A p hx).hom.cell j) (ρ_ (A ys[j])).hom := by
  let e := wordEquiv p.perm hx
  let q := wordComparisonCells A A p hx (fun x => Iso.refl (A x))
  have h := nativeSingletonMap_cell_heq (A:=wordFamily A xs) (B:=wordFamily A ys) e (fun k => (q k).hom) j
  change HEq ((wordReorderIso A p hx).hom.cell j)
    ((ρ_ (A xs[e.symm j])).hom ≫ (q j).hom) at h
  have a : A xs[e.symm j] = A ys[j] := congrArg A (wordEquiv_get_symm p.perm hx j)
  have b : HEq (ρ_ (A xs[e.symm j])).hom (ρ_ (A ys[j])).hom := by rw [a]
  have c : HEq (q j).hom (𝟙 (A ys[j])) := hom_source_pin_heq a _
  have d := structural_seq_heq (K:=coeff (C:=C)) (congrArg (fun z => z ⊗ Zₐ) a) a rfl b c
  exact h.trans (d.trans (heq_of_eq (Category.comp_id _)))

set_option backward.isDefEq.respectTransparency false in
theorem wordReorder_decode_heq {W : Type u} [DecidableEq W] (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) (hx : xs.Nodup) (y : W) (hy : y ∈ ys) :
    HEq (decodeNativeWordCell A A id (fun _ h => p.perm.mem_iff.mp h)
      (p.perm.nodup hx) (wordReorderIso A p hx).hom (wordReorder_carrier A p hx) y hy)
      (ρ_ (A y)).hom := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hy
  let j : Fin ys.length := ⟨i,hi⟩
  change HEq (decodeNativeWordCell A A id _ _ _ _ ys[j] (List.getElem_mem _)) (ρ_ (A ys[j])).hom
  rw [decodeNativeWordCell_get _ _ _ _ _ _ _ j]
  unfold readNativeWordCell
  exact (hom_source_pin_heq _ _).trans (wordReorder_cell_heq A p hx j)

section ReorderArrow
variable (D : OrderedDependentAugData I) {xs : List D.X} {us : D.X → List D.U}
variable (e : AddressOrder D.X D.xs xs) (d : ∀ x, AddressOrder D.U (D.us x) (us x))

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentAugData.reorderMap :
    @OrderedDependentMap C _ _ _ D.X D.U D.X D.U D.eqX D.eqU D.xs D.us xs us D.V D.A D.V D.A :=
  letI := D.eqX
  letI := D.eqU
  { parent := id
    child := fun _ => id
    parent_mem := fun _ h => e.perm.mem_iff.mp h
    child_mem := fun x _ _ h => (d x).perm.mem_iff.mp h
    outer := decodeNativeWordCell D.V D.V id (fun _ h => e.perm.mem_iff.mp h)
      (e.perm.nodup D.xs_unique) (wordReorderIso D.V e D.xs_unique).hom (wordReorder_carrier D.V e D.xs_unique)
    inner := fun x hx =>
      decodeNativeWordCell (D.A x) (D.A x) id (fun _ h => (d x).perm.mem_iff.mp h)
        ((d x).perm.nodup (D.us_unique x hx)) (wordReorderIso (D.A x) (d x) (D.us_unique x hx)).hom
        (wordReorder_carrier (D.A x) (d x) (D.us_unique x hx)) }

set_option linter.style.haveILetI false in
theorem OrderedDependentAugData.reorderMap_outer :
    letI := D.eqX
    letI := D.eqU
    (D.reorderMap e d).outerNative (D.reorder e d).xs_unique = (wordReorderIso D.V e D.xs_unique).hom := by
  letI := D.eqX
  letI := D.eqU
  exact decodeNativeWordCell_reassemble _ _ _ _ _ _ _

set_option linter.style.haveILetI false in
theorem OrderedDependentAugData.reorderMap_inner (x : D.X) (hx : x ∈ D.xs) :
    letI := D.eqX
    letI := D.eqU
    (D.reorderMap e d).innerNative x hx ((d x).perm.nodup (D.us_unique x hx)) =
      (wordReorderIso (D.A x) (d x) (D.us_unique x hx)).hom := by
  letI := D.eqX
  letI := D.eqU
  exact decodeNativeWordCell_reassemble _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
noncomputable def OrderedDependentAugData.reorderArrow :
    OrderedDependentAugArrow D (D.reorder e d) where
  map := D.reorderMap e d
  preserves := by
    letI := D.eqX
    letI := D.eqU
    constructor
    · rw [D.reorderMap_outer e d]
      exact wordReorder_preserves D.V e D.xs_unique D.ε
    · intro x hx
      rw [D.reorderMap_inner e d x hx]
      exact wordReorder_preserves (D.A x) (d x) (D.us_unique x hx) (D.δ x)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
include hl hr in
theorem OrderedDependentAugData.reorderMap_cell_heq
    (p : D.X × D.U) (hp : p ∈ dependentWord xs us) :
    letI := D.eqX
    letI := D.eqU
    HEq (origDependentCell (D.reorderMap e d) R L p hp)
      (ρ_ (dependentLabels (T:=T) D.V D.A p)).hom := by
  letI := D.eqX
  letI := D.eqU
  let M := D.reorderMap e d
  let k := (dependentWord_mem xs us p).mp hp
  let h₀ : p.1 ∈ D.xs := e.perm.mem_iff.mpr k.1
  let h₁ : p.2 ∈ D.us p.1 := (d p.1).perm.mem_iff.mpr k.2
  let x : M.Slice p.1 := ⟨p.1,h₀,rfl⟩
  let y := p.2
  have a : M.slice p.1 = [x] := by
    have h : (M.slice p.1).map Subtype.val = [p.1] :=
      (sliceWord_map D.xs M.parent p.1).trans (wordFibre_identity_singleton D.xs_unique h₀)
    generalize M.slice p.1 = s at h ⊢
    cases s with
    | nil => simp at h
    | cons b l =>
      simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at h
      rcases h with ⟨hb,rfl⟩
      exact congrArg (fun w : M.Slice p.1 => [w]) (Subtype.ext hb)
  have b : M.terms p.1 p.2 x = [y] := wordFibre_identity_singleton (D.us_unique p.1 h₀) h₁
  let V := M.parentVal p.1 x
  let W := M.childVal p.1 x y
  let _ : (leftFactor T V).LaxBraided := lF V
  let _ : (rightFactor (T:=T) W).LaxBraided := rF W
  have ar : HEq (M.locOuter p.1 k.1) (ρ_ V).hom := by
    exact (hom_source_pin_heq _ _).trans (wordReorder_decode_heq D.V e D.xs_unique p.1 k.1)
  have br : HEq (M.locInner p.1 p.2 k.2 x) (ρ_ W).hom := by
    exact (hom_source_pin_heq _ _).trans ((hom_target_pin_heq _ _).trans
      (wordReorder_decode_heq (D.A p.1) (d p.1) (D.us_unique p.1 h₀) p.2 k.2))
  have z := dependentLocal_singleton_heq R L (M.parentVal p.1) (M.childVal p.1)
    (M.slice p.1) (M.terms p.1 p.2) x y a b (hl V) (hr W)
    (M.locInner p.1 p.2 k.2) (M.locOuter p.1 k.1) ar br
  unfold origDependentCell localCellToGlobal
  exact (hom_source_pin_heq _ _).trans z

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
include hl hr in
theorem OrderedDependentAugData.reorderMap_accumulated_native :
    letI := D.eqX
    letI := D.eqU
    origDependentWordMap (D.reorderMap e d) R L
      (dependentWord_nodup (D.reorder e d).xs_unique (D.reorder e d).us_unique) =
    (wordReorderIso (dependentLabels (T:=T) D.V D.A) (dependentOrder e d)
      (dependentWord_nodup D.xs_unique D.us_unique)).hom := by
  letI := D.eqX
  letI := D.eqU
  let M := D.reorderMap e d
  let G := dependentLabels (T:=T) D.V D.A
  let n := dependentWord_nodup D.xs_unique D.us_unique
  let o := dependentOrder e d
  apply native_hom_eq_of_cell_heq
  · change wordCarrier (origDepCarrier M) (origDepCarrier_support M) _ = _
    apply wordCarrier_eq_of_get
    intro i
    change (dependentWord xs us)[(wordEquiv o.perm n) i] =
      origDepCarrier M (dependentWord D.xs D.us)[i]
    rw [wordEquiv_get o.perm n]
    rfl
  · intro j
    change HEq (eqToHom _ ≫ origDependentCell M R L (dependentWord xs us)[j] (List.getElem_mem _)) _
    exact (hom_source_pin_heq _ _).trans
      ((D.reorderMap_cell_heq e d R L hl hr (dependentWord xs us)[j] (List.getElem_mem _)).trans
        (wordReorder_cell_heq G o n j).symm)

variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)

set_option backward.isDefEq.respectTransparency false in
/-- The order transition is an actual native augmented isomorphism, with the
literal reindexing of the raw dependent addresses as its underlying arrow. -/
noncomputable def OrderedDependentAugData.accumulatedReorderIso :
    NativeAugmentedIso (D.accumulate R L J) ((D.reorder e d).accumulate R L J) := by
  let p := (D.reorderArrow e d).accumulate R L J N NL hl
  let q := wordReorderIso (dependentLabels (T:=T) D.V D.A) (dependentOrder e d)
    (dependentWord_nodup D.xs_unique D.us_unique)
  have h : p.native = q.hom := D.reorderMap_accumulated_native e d R L hl hr
  exact q.augment (h ▸ p.preserves)

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.accumulatedReorderIso_hom :
    (D.accumulatedReorderIso e d R L hl hr J N NL).hom =
      (D.reorderArrow e d).accumulate R L J N NL hl := by
  apply AugHom.ext
  exact (D.reorderMap_accumulated_native e d R L hl hr).symm

end ReorderArrow

section Transport
variable {X Y : Type u} [DecidableEq Y] {xs xs' : List X} {ys ys' : List Y} {f : X → Y}
variable (A : X → C) (B : Y → C) (ps : AddressOrder X xs xs') (pt : AddressOrder Y ys ys')
variable (hx : xs.Nodup) (hy : ys.Nodup)

set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_reorder_preserves (h : ∀ x ∈ xs, f x ∈ ys)
    (p : ∀ y ∈ ys, fold 𝒮 Zₐ A (wordFibre xs f y) ⟶ B y)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (hp : (wordNativeMap f h hy A B (fun j => p ys[j] (List.getElem_mem _))).comp
        (wordAug B ys b).ε = (wordAug A xs a).ε) :
    (wordNativeMap f (wordReorder_support ps pt h) (pt.perm.nodup hy) A B
      (fun j => wordNativeMap_reorderCell A B ps pt hx p ys'[j] (List.getElem_mem _))).comp
        (wordAug B ys' ((orderSumIso B pt).inv ≫ b)).ε =
      (wordAug A xs' ((orderSumIso A ps).inv ≫ a)).ε := by
  have sq := wordNativeMap_reorder A B ps pt hx hy h p
  have hs := wordReorder_preserves A ps hx a
  have ht := wordReorder_preserves B pt hy b
  let i := wordReorderIso A ps hx
  let j := wordReorderIso B pt hy
  have h' :
      i.hom.comp ((wordNativeMap f (wordReorder_support ps pt h) (pt.perm.nodup hy) A B
        (fun j => wordNativeMap_reorderCell A B ps pt hx p ys'[j] (List.getElem_mem _))).comp
          (wordAug B ys' ((orderSumIso B pt).inv ≫ b)).ε) =
      i.hom.comp (wordAug A xs' ((orderSumIso A ps).inv ≫ a)).ε := by
    rw [← Hom.comp_assoc, ← sq, Hom.comp_assoc, ht, hp, hs]
  have h'' := congrArg (fun u => i.inv.comp u) h'
  simpa only [← Hom.comp_assoc, i.inv_hom, Hom.ident_comp] using h''

end Transport

namespace OrderedDependentAugArrow
variable {D E F : OrderedDependentAugData I}

set_option backward.isDefEq.respectTransparency false in
noncomputable def comp (p : OrderedDependentAugArrow D E) (q : OrderedDependentAugArrow E F) :
    OrderedDependentAugArrow D F :=
  letI := E.eqX
  letI := E.eqU
  letI := F.eqX
  letI := F.eqU
  let h := fun x hx => E.us_unique _ (p.map.parent_mem x hx)
  let k := fun y hy => F.us_unique _ (q.map.parent_mem y hy)
  ⟨p.map.compose q.map E.xs_unique F.xs_unique h k,
    p.map.compose_preserves q.map E.xs_unique F.xs_unique h k p.preserves q.preserves⟩

theorem ext_map {p q : OrderedDependentAugArrow D E} (h : p.map = q.map) : p = q := by
  cases p
  cases q
  cases h
  rfl

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
include NR hr in
theorem accumulate_comp (p : OrderedDependentAugArrow D E) (q : OrderedDependentAugArrow E F) :
    (p.comp q).accumulate R L J N NL hl =
      (p.accumulate R L J N NL hl).comp (q.accumulate R L J N NL hl) := by
  letI := D.eqX
  letI := E.eqX
  letI := E.eqU
  letI := F.eqX
  letI := F.eqU
  exact OrderedDependentMap.accumulateAug_comp R L J p.map q.map N NR NL hl hr
    D.xs_unique E.xs_unique F.xs_unique D.us_unique E.us_unique F.us_unique p.preserves q.preserves

end OrderedDependentAugArrow

section TransportArrow
variable {D E : OrderedDependentAugData I}
variable {xs : List D.X} {us : D.X → List D.U} {ys : List E.X} {vs : E.X → List E.U}
variable (e : AddressOrder D.X D.xs xs) (d : ∀ x, AddressOrder D.U (D.us x) (us x))
variable (f : AddressOrder E.X E.xs ys) (g : ∀ y, AddressOrder E.U (E.us y) (vs y))
variable (p : OrderedDependentAugArrow D E)

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentAugArrow.reorderMap :
    @OrderedDependentMap C _ _ _ D.X D.U E.X E.U E.eqX E.eqU xs us ys vs D.V D.A E.V E.A :=
  letI := E.eqX
  letI := E.eqU
  { parent := p.map.parent
    child := p.map.child
    parent_mem := wordReorder_support e f p.map.parent_mem
    child_mem := fun x hx =>
      wordReorder_support (d x) (g (p.map.parent x)) (p.map.child_mem x (e.perm.mem_iff.mpr hx))
    outer := wordNativeMap_reorderCell D.V E.V e f D.xs_unique p.map.outer
    inner := fun x hx =>
      let hx' := e.perm.mem_iff.mpr hx
      wordNativeMap_reorderCell (D.A x) (E.A (p.map.parent x)) (d x) (g (p.map.parent x))
        (D.us_unique x hx') (p.map.inner x hx') }

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
noncomputable def OrderedDependentAugArrow.reorder :
    OrderedDependentAugArrow (D.reorder e d) (E.reorder f g) where
  map := OrderedDependentAugArrow.reorderMap (D:=D) (E:=E) e d f g p
  preserves := by
    letI := E.eqX
    letI := E.eqU
    constructor
    · exact wordNativeMap_reorder_preserves D.V E.V e f D.xs_unique E.xs_unique
        p.map.parent_mem p.map.outer D.ε E.ε p.preserves.outer
    · intro x hx
      have hx' : x ∈ D.xs := e.perm.mem_iff.mpr hx
      let y := p.map.parent x
      exact wordNativeMap_reorder_preserves (D.A x) (E.A y) (d x) (g y) (D.us_unique x hx')
        (E.us_unique y (p.map.parent_mem x hx')) (p.map.child_mem x hx') (p.map.inner x hx')
        (D.δ x) (E.δ y) (p.preserves.inner x hx')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
set_option linter.style.haveILetI false in
theorem OrderedDependentAugArrow.reorder_square :
    p.comp (E.reorderArrow f g) = (D.reorderArrow e d).comp (p.reorder e d f g) := by
  letI := D.eqX
  letI := D.eqU
  letI := E.eqX
  letI := E.eqU
  let D' := D.reorder e d
  let E' := E.reorder f g
  let a := D.reorderArrow e d
  let b := E.reorderArrow f g
  let q := p.reorder e d f g
  apply OrderedDependentAugArrow.ext_map
  refine OrderedDependentMap.ext_of_native (p.comp b).map (a.comp q).map E'.xs_unique E'.us_unique
    rfl rfl ?_ ?_
  · have h₀ := p.map.compose_outer b.map E.xs_unique E'.xs_unique
        (fun x hx => E.us_unique _ (p.map.parent_mem x hx))
        (fun y hy => E'.us_unique _ (b.map.parent_mem y hy))
    have h₁ := a.map.compose_outer q.map D'.xs_unique E'.xs_unique
        (fun x hx => D'.us_unique _ (a.map.parent_mem x hx))
        (fun y hy => E'.us_unique _ (q.map.parent_mem y hy))
    change (p.comp b).map.outerNative E'.xs_unique = _ at h₀
    change (a.comp q).map.outerNative E'.xs_unique = _ at h₁
    rw [h₀, h₁]
    change (p.map.outerNative E.xs_unique).comp ((E.reorderMap f g).outerNative E'.xs_unique) =
      ((D.reorderMap e d).outerNative D'.xs_unique).comp (q.map.outerNative E'.xs_unique)
    rw [E.reorderMap_outer f g, D.reorderMap_outer e d]
    exact wordNativeMap_reorder D.V E.V e f D.xs_unique E.xs_unique p.map.parent_mem p.map.outer
  · intro x hx
    apply heq_of_eq
    let y := p.map.parent x
    have hy : y ∈ E.xs := p.map.parent_mem x hx
    have hx' : x ∈ D'.xs := e.perm.mem_iff.mp hx
    have h₀ := p.map.compose_inner b.map E.xs_unique E'.xs_unique
        (fun x hx => E.us_unique _ (p.map.parent_mem x hx))
        (fun y hy => E'.us_unique _ (b.map.parent_mem y hy)) x hx
    have h₁ := a.map.compose_inner q.map D'.xs_unique E'.xs_unique
        (fun x hx => D'.us_unique _ (a.map.parent_mem x hx))
        (fun y hy => E'.us_unique _ (q.map.parent_mem y hy)) x hx
    change (p.comp b).map.innerNative x hx _ = _ at h₀
    change (a.comp q).map.innerNative x hx _ = _ at h₁
    rw [h₀, h₁]
    change (p.map.innerNative x hx (E.us_unique y hy)).comp
        ((E.reorderMap f g).innerNative y hy _) =
      ((D.reorderMap e d).innerNative x hx _).comp (q.map.innerNative x hx' _)
    rw [E.reorderMap_inner f g y hy, D.reorderMap_inner e d x hx]
    exact wordNativeMap_reorder (D.A x) (E.A y) (d x) (g y)
      (D.us_unique x hx) (E.us_unique y hy) (p.map.child_mem x hx) (p.map.inner x hx)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
include NR hr in
/-- Actual accumulated maps commute with transport by additive presentation.
The two horizontal maps use independently built whole-fibre cells. -/
theorem OrderedDependentAugArrow.accumulate_reorder_square :
    (p.accumulate R L J N NL hl).comp ((E.reorderArrow f g).accumulate R L J N NL hl) =
      ((D.reorderArrow e d).accumulate R L J N NL hl).comp ((p.reorder e d f g).accumulate R L J N NL hl) := by
  rw [← OrderedDependentAugArrow.accumulate_comp R L J N NR NL hl hr,
    ← OrderedDependentAugArrow.accumulate_comp R L J N NR NL hl hr,
    p.reorder_square e d f g]

set_option backward.isDefEq.respectTransparency false in
include NR in
theorem OrderedDependentAugArrow.accumulatedReorderIso_natural :
    (p.accumulate R L J N NL hl).comp (E.accumulatedReorderIso f g R L hl hr J N NL).hom =
      (D.accumulatedReorderIso e d R L hl hr J N NL).hom.comp
        ((p.reorder e d f g).accumulate R L J N NL hl) := by
  rw [E.accumulatedReorderIso_hom, D.accumulatedReorderIso_hom]
  exact p.accumulate_reorder_square e d f g R L J N NR NL hl hr

end TransportArrow

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
