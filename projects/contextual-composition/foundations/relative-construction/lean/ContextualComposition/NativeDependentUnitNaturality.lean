module
public import ContextualComposition.NativeDependentTriangle
@[expose] public section

/-! Unit compatibility with arbitrary selected whole cells. These results
retain empty source fibres, since the unit laws are nullary as well as
binary and do not require uniqueness of morphisms from the additive unit. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)

set_option backward.isDefEq.respectTransparency false in
/-- Moving the right unitor past an arbitrary whole parent cell. -/
theorem rightUnit_whole_cell (A : X → C) (xs : List X) {B : C}
    (α : fold 𝒮 Zₐ A xs ⟶ B) :
    (Lin.right R I).collect A xs ≫ T.map α (𝟙 I) ≫ J.ρ B =
      act 𝒮 Zₐ (fun x => J.ρ (A x)) xs ≫ α := by
  have h : T.map α (𝟙 I) ≫ J.ρ B = J.ρ (fold 𝒮 Zₐ A xs) ≫ α := J.natural α
  have k : (Lin.right R I).collect A xs ≫ J.ρ (fold 𝒮 Zₐ A xs) =
      act 𝒮 Zₐ (fun x => J.ρ (A x)) xs := by
    rw [collect_right_eq]
    exact gather_unit J A xs
  rw [h, reassoc_of% k]

set_option backward.isDefEq.respectTransparency false in
include Q in
/-- Moving the left unitor past an arbitrary whole continuation cell. -/
theorem leftUnit_whole_cell (A : X → C) (xs : List X) {B : C}
    (α : fold 𝒮 Zₐ A xs ⟶ B) :
    (Lin.left L I).collect A xs ≫ T.map (𝟙 I) α ≫ depLeftUnitCell R J P B =
      act 𝒮 Zₐ (fun x => depLeftUnitCell R J P (A x)) xs ≫ α := by
  rw [depLeftUnitCell_natural R J P α, reassoc_of% depLeftUnit_collect R L J P Q A xs]


section Lift
variable {Y : Type u} [DecidableEq Y] {xs : List X} {ys : List Y}
variable (I : C) (A : X → C) (B : Y → C)
variable (f : X → Y) (hs : ∀ x ∈ xs, f x ∈ ys)
variable (α : ∀ y ∈ ys, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A (wordFibre xs f y) ⟶ B y)

local notation "uLab" => (fun _ _ => I)

set_option backward.isDefEq.respectTransparency false in
/-- Lift the parent arrow without imposing any condition on its
carrier or its original whole cells. Every constant child is the
identity on the single unit occurrence. -/
def rightUnitLiftInput :
    OrderedDependentMap xs (fun _ => ([PUnit.unit] : List PUnit.{u+1}))
      ys (fun _ => ([PUnit.unit] : List PUnit.{u+1})) A uLab B uLab where
  parent := f
  child := fun _ => id
  parent_mem := hs
  child_mem := fun _ _ _ hu => hu
  outer := α
  inner := fun _ _ y hy => by
    have h : y = PUnit.unit := Subsingleton.elim _ _
    subst y
    exact (ρ_ I).hom

set_option backward.isDefEq.respectTransparency false in
theorem rightUnitLiftInput_terms (y : Y) (t : PUnit.{u+1})
    (x : (rightUnitLiftInput I A B f hs α).Slice y) :
    (rightUnitLiftInput I A B f hs α).terms y t x = [PUnit.unit] := by
  have h : t = PUnit.unit := Subsingleton.elim _ _
  subst t
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem rightUnitLiftInput_inner (y : Y) (t : PUnit.{u+1})
    (ht : t ∈ [PUnit.unit]) (x : (rightUnitLiftInput I A B f hs α).Slice y) :
    HEq ((rightUnitLiftInput I A B f hs α).innerSliceCell x t ht) (ρ_ I).hom := by
  have h : t = PUnit.unit := Subsingleton.elim _ _
  subst t
  unfold OrderedDependentMap.innerSliceCell OrderedDependentMap.locInner rightUnitLiftInput
  simp


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
theorem rightUnitLiftInput_cell
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lax : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (y : Y) (hy : y ∈ ys) :
    HEq (origDependentCell (rightUnitLiftInput I A B f hs α) R L (y,PUnit.unit)
      ((dependentWord_mem _ _ _).mpr ⟨hy,List.mem_cons_self⟩))
      ((Lin.right R I).collect A (wordFibre xs f y) ≫ T.map (α y hy) (𝟙 I)) := by
  let D := rightUnitLiftInput I A B f hs α
  let h₀ := ((dependentWord_mem ys (fun _ => [PUnit.unit]) (y,PUnit.unit)).mpr ⟨hy,List.mem_cons_self⟩)
  let S := D.Slice y
  let s := D.slice y
  let j : S → X × PUnit.{u+1} := fun x => (x.val,PUnit.unit)
  let G := dependentLabels (T:=T) A (fun _ (_ : PUnit.{u+1}) => I)
  let F := fold 𝒮 Zₐ G
  let W := wordFibre (dependentWord xs (fun _ => [PUnit.unit])) (origDepCarrier D) (y,PUnit.unit)
  let r (x : S) := (ρ_ (G (j x))).hom
  let g := fun (x : S) (t : PUnit.{u+1}) => (x.val,t)
  let m := fun (_ : S) => ([PUnit.unit] : List PUnit.{u+1})
  let u := fun x => eqToHom (std_fold_map G (g x) (m x))
  let A₀ := A ∘ (Subtype.val : S → X)
  let v := (Lin.right R I).collect A₀ s
  let p := D.locOuter y hy
  have hr (x : S) : attachedSliceChildCell D L x PUnit.unit (List.mem_cons_self) = r x := by
    have k := rightUnitLiftInput_inner I A B f hs α y PUnit.unit List.mem_cons_self x
    have e : D.innerSliceCell x PUnit.unit List.mem_cons_self = (ρ_ I).hom := eq_of_heq k
    have f₀ := gatherLeft_singleton_unit L (A x.val) I (hl _)
    unfold attachedSliceChildCell
    rw [e]
    exact f₀
  have h := origDependentCell_flatRows D R L (y,PUnit.unit) h₀
  have P₀ : s.flatMap (fun x => [j x]) = W := by
    have e := dependentSlice_word_raw D (y,PUnit.unit)
    unfold dependentWord at e
    rw [List.map_flatMap] at e
    simp only [List.map_map] at e
    change s.flatMap (fun x => [j x]) = W at e
    exact e
  change origDependentCell D R L (y,PUnit.unit) h₀ =
    eqToHom (congrArg F P₀.symm) ≫ taggedRaggedRows G g m s ≫
      act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x PUnit.unit List.mem_cons_self) s ≫
      DependentFibre.gather R A₀ I s ≫ T.map p (𝟙 I) at h
  rw [h, show (fun x => attachedSliceChildCell D L x PUnit.unit List.mem_cons_self) = r from funext hr]
  unfold taggedRaggedRows
  have ev : act 𝒮 Zₐ u s ≫ act 𝒮 Zₐ r s = act 𝒮 Zₐ (fun x => u x ≫ r x) s := act_seq 𝒮 Zₐ u r s
  simp only [Category.assoc]
  rw [← Category.assoc (act 𝒮 Zₐ u s), ev]
  let e₀ := congrArg F (flatMap_single_eq_map j s).symm
  let e₁ := std_fold_map G j s
  have hc := rowsChart_mapped_singletons G j (fun x => (m x).map (g x)) (fun _ => rfl) s
  change eqToHom e₀ ≫ rowsChart G (fun x => (m x).map (g x)) s ≫
    act 𝒮 Zₐ (fun x => u x ≫ r x) s = eqToHom e₁ at hc
  let e₂ := congrArg F ((flatMap_single_eq_map j s).symm.trans P₀)
  have eqP : congrArg F P₀.symm = e₂.symm.trans e₀ := Subsingleton.elim _ _
  rw [eqP, ← eqToHom_trans e₂.symm e₀]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  let pin := e₂.symm.trans e₁
  rw [eqToHom_trans_assoc]
  have hlift : HEq (eqToHom pin ≫ v ≫ T.map p (𝟙 I)) (v ≫ T.map p (𝟙 I)) :=
    hom_source_pin_heq pin _
  have hα : HEq p (α y hy) := hom_source_pin_heq _ _
  let eo := (std_fold_map A Subtype.val s).symm.trans
    (congrArg (fold 𝒮 Zₐ A) (sliceWord_map xs f y))
  have vg : HEq v ((Lin.right R I).collect A (wordFibre xs f y)) := by
    have t := linCollect_map_heq (Lin.right R I) A Subtype.val s
    have hm : s.map Subtype.val = wordFibre xs f y := sliceWord_map xs f y
    rw [hm] at t
    exact t
  have xa : fold 𝒮 Zₐ (fun x => T.obj (A₀ x) I) s =
      fold 𝒮 Zₐ (fun x => T.obj (A x) I) (wordFibre xs f y) :=
    (std_fold_map (fun x => T.obj (A x) I) Subtype.val s).symm.trans
      (congrArg (fold 𝒮 Zₐ (fun x => T.obj (A x) I)) (sliceWord_map xs f y))
  have hh := structural_map_heq (S:=T) eo (rfl : B y = B y) (rfl : I = I) (rfl : I = I)
    hα (HEq.rfl : HEq (𝟙 I) (𝟙 I))
  rw [← collect_right_eq]
  exact hlift.trans (structural_seq_heq (K:=coeff (C:=C)) xa (congrArg (fun n => T.obj n I) eo) rfl vg hh)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
theorem rightUnitLiftInput_native_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lax : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (hy : ys.Nodup) :
    HEq
      (origDependentWordMap (rightUnitLiftInput I A B f hs α) R L
        (dependentWord_nodup hy (fun _ _ => by simp)))
      (wordNativeMap f hs hy (fun x => T.obj (A x) I) (fun y => T.obj (B y) I)
        (fun j => (Lin.right R I).collect A (wordFibre xs f ys[j]) ≫ T.map (α ys[j] (List.getElem_mem _)) (𝟙 I))) := by
  let D := rightUnitLiftInput I A B f hs α
  let F₀ := fun x => T.obj (A x) I
  let F₁ := fun y => T.obj (B y) I
  let w₀ := dependentWord xs (fun _ => ([PUnit.unit] : List PUnit.{u+1}))
  let w₁ := dependentWord ys (fun _ => ([PUnit.unit] : List PUnit.{u+1}))
  let φ := fun j : Fin w₁.length => origDependentCell D R L w₁[j] (List.getElem_mem _)
  let ψ (j : Fin ys.length) := (Lin.right R I).collect A (wordFibre xs f ys[j]) ≫
    T.map (α ys[j] (List.getElem_mem _)) (𝟙 I)
  have ex : w₀.map Prod.fst = xs := triangleReadParent xs
  have ey : w₁.map Prod.fst = ys := triangleReadParent ys
  change HEq (wordNativeMap (origDepCarrier D) (origDepCarrier_support D) _
    (F₀ ∘ Prod.fst) (F₁ ∘ Prod.fst) φ) (wordNativeMap f hs hy F₀ F₁ ψ)
  apply readWordNativeMap_heq F₀ F₁ Prod.fst Prod.fst (origDepCarrier D) f
    (origDepCarrier_support D) hs _ hy ex ey (fun _ _ => rfl) φ ψ
  intro j
  let k := Fin.cast ((List.length_map (Prod.fst : Y × PUnit.{u+1} → Y)).symm.trans (congrArg List.length ey)) j
  let y := w₁[j].1
  have e : y = ys[k] := retag_word_get Prod.fst w₁ ey j
  have i : w₁[j] = (y,PUnit.unit) := Prod.ext rfl (Subsingleton.elim _ _)
  let w (t : Y × PUnit.{u+1}) (h : t ∈ w₁) := origDependentCell D R L t h
  have h {a b : Y × PUnit.{u+1}} (e : a = b) (ha : a ∈ w₁) (hb : b ∈ w₁) :
      HEq (w a ha) (w b hb) := by subst b; rfl
  exact (h (i.trans (congrArg (fun c => (c,PUnit.unit)) e)) (List.getElem_mem _)
      ((dependentWord_mem _ _ _).mpr ⟨List.getElem_mem _,List.mem_cons_self⟩)).trans
    (rightUnitLiftInput_cell I A B f hs α R L hl ys[k] (List.getElem_mem _))


set_option backward.isDefEq.respectTransparency false in
theorem dependentRightUnitIso_pointwise_heq {Z : Type u}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    (xs : List Z) (V : Z → C) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    [lax : ∀ x, (leftFactor T (V x)).LaxBraided] (hl : ∀ x, SameLeftGather T (V x) L)
    (iρ : ∀ a, IsIso (J.ρ a)) (hn : xs.Nodup) :
    HEq (dependentRightUnitIso R L J xs V ε hl iρ hn).hom.native
      (wordPointwise xs (fun x => J.ρ (V x))) := by
  unfold dependentRightUnitIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (wordAugIso_ident_pointwise _ _ _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
/-- Native naturality of the right unit on arbitrary carrier-changing
inputs. The lift is the original dependent map with identity singleton
continuations, not a separately defined coefficientwise substitute. -/
theorem rightUnit_original_native_square
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    [lax : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (iρ : ∀ c, IsIso (J.ρ c)) (hx : xs.Nodup) (hy : ys.Nodup) :
    (origDependentWordMap (rightUnitLiftInput I A B f hs α) R L
      (dependentWord_nodup hy (fun _ _ => by simp))).comp
      (dependentRightUnitIso R L J ys B b (fun y => hl (B y)) iρ hy).hom.native =
    (dependentRightUnitIso R L J xs A a (fun x => hl (A x)) iρ hx).hom.native.comp
      (wordNativeMap f hs hy A B (fun y => α ys[y] (List.getElem_mem _))) := by
  let F₀ := fun x => T.obj (A x) I
  let F₁ := fun y => T.obj (B y) I
  let p (y : Y) (hm : y ∈ ys) := (Lin.right R I).collect A (wordFibre xs f y) ≫ T.map (α y hm) (𝟙 I)
  let e₀ (x : X) : F₀ x ≅ A x := by
    let _ := iρ (A x)
    exact asIso (J.ρ (A x))
  let e₁ (y : Y) : F₁ y ≅ B y := by
    let _ := iρ (B y)
    exact asIso (J.ρ (B y))
  let g := origDependentWordMap (rightUnitLiftInput I A B f hs α) R L
    (dependentWord_nodup hy (fun _ _ => by simp))
  let k := wordNativeMap f hs hy F₀ F₁ (fun j => p ys[j] (List.getElem_mem _))
  let q := wordNativeMap f hs hy A B (fun j => α ys[j] (List.getElem_mem _))
  let u := (dependentRightUnitIso R L J xs A a (fun x => hl (A x)) iρ hx).hom.native
  let v := (dependentRightUnitIso R L J ys B b (fun y => hl (B y)) iρ hy).hom.native
  have h := wordNativeMap_identChart_square f hs hx hy F₀ A F₁ B e₀ e₁ p α
    (fun y hy => by unfold p; rw [Category.assoc]; exact rightUnit_whole_cell R J A (wordFibre xs f y) (α y hy))
  rw [wordReindex_ident_pointwise, wordReindex_ident_pointwise] at h
  have ex := wordFamily_read_eq F₀ Prod.fst _ xs (triangleReadParent xs)
  have ey := wordFamily_read_eq F₁ Prod.fst _ ys (triangleReadParent ys)
  have hg : HEq g k := rightUnitLiftInput_native_heq I A B f hs α R L hl hy
  have hu := dependentRightUnitIso_pointwise_heq I R L J xs A a (fun x => hl (A x)) iρ hx
  have hv := dependentRightUnitIso_pointwise_heq I R L J ys B b (fun y => hl (B y)) iρ hy
  change g.comp v = u.comp q
  exact eq_of_heq ((nativeHom_comp_heq g v k _ ex ey rfl hg hv).trans
    ((heq_of_eq h).trans (nativeHom_comp_heq u q _ q ex rfl rfl hu HEq.rfl).symm))


set_option backward.isDefEq.respectTransparency false in
theorem rightUnitLiftInput_innerNative (x : X) (hx : x ∈ xs)
    (h₀ : ([PUnit.unit] : List PUnit.{u+1}).Nodup) :
    (rightUnitLiftInput I A B f hs α).innerNative x hx h₀ =
      Hom.ident (wordFamily (fun _ : PUnit.{u+1} => I) [PUnit.unit]) := by
  let D := rightUnitLiftInput I A B f hs α
  unfold OrderedDependentMap.innerNative
  apply wordNativeMap_ident_of_singleton h₀ (fun _ : PUnit.{u+1} => I) id _ (fun _ _ => rfl)
  intro j
  let t := ([PUnit.unit] : List PUnit.{u+1})[j]
  have e : t = PUnit.unit := Subsingleton.elim _ _
  let p (u : PUnit.{u+1}) (hu : u ∈ [PUnit.unit]) := D.inner x hx u hu
  have h {u v : PUnit.{u+1}} (e : u = v) (hu : u ∈ [PUnit.unit]) (hv : v ∈ [PUnit.unit]) :
      HEq (p u hu) (p v hv) := by subst v; rfl
  exact (h e (List.getElem_mem _) List.mem_cons_self).trans HEq.rfl

set_option backward.isDefEq.respectTransparency false in
theorem singleton_indexedAugmentation_eq {Z : Type u} :
    indexedAugmentation (B:=fun (_ : Z) (_ : PUnit.{u+1}) => I)
      (us:=fun _ => [PUnit.unit]) (fun _ => (ρ_ I).hom) = fun _ => (ρ_ I).hom := by
  funext z
  change eqToHom (rfl : I ⊗ Zₐ = I ⊗ Zₐ) ≫ (ρ_ I).hom = (ρ_ I).hom
  simp

section AugmentedLift
variable [DecidableEq X]
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lax : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (hx : xs.Nodup) (hy : ys.Nodup)
variable (h : (wordNativeMap f hs hy A B (fun j => α ys[j] (List.getElem_mem _))).comp
  (wordAug B ys b).ε = (wordAug A xs a).ε)
local notation "unitIn" => (fun _ => [PUnit.unit])
set_option quotPrecheck false in
local notation "unitAug" => (fun _ => (ρ_ I).hom)

set_option backward.isDefEq.respectTransparency false in
noncomputable def rightUnitLiftAugMap :
    AugHom ℙ (dependentWordAug R L J xs unitIn A uLab unitAug a)
      (dependentWordAug R L J ys unitIn B uLab unitAug b) where
  native := origDependentWordMap (rightUnitLiftInput I A B f hs α) R L
    (dependentWord_nodup hy (fun _ _ => by simp))
  preserves := by
    let D := rightUnitLiftInput I A B f hs α
    have p : D.Preserves hy (fun _ _ => by simp)
        (fun _ => (ρ_ I).hom) (fun _ => (ρ_ I).hom) a b := by
      refine ⟨h, ?_⟩
      intro x hx
      rw [rightUnitLiftInput_innerNative I A B f hs α x hx _]
      exact Hom.ident_comp _
    let q := D.accumulateAug R L J N NL hl hx hy (fun _ _ => by simp) (fun _ _ => by simp) p
    have t := q.preserves
    change (origDependentWordMap D R L (dependentWord_nodup hy (fun _ _ => by simp))).comp
        (dependentWordAug R L J ys unitIn B uLab (indexedAugmentation unitAug) b).ε =
      (dependentWordAug R L J xs unitIn A uLab (indexedAugmentation unitAug) a).ε at t
    rw [singleton_indexedAugmentation_eq I, singleton_indexedAugmentation_eq I] at t
    exact t

set_option backward.isDefEq.respectTransparency false in
theorem rightUnit_original_augmented_square (iρ : ∀ c, IsIso (J.ρ c)) :
    (rightUnitLiftAugMap I A B f hs α R L J N NL hl a b hx hy h).comp
      (dependentRightUnitIso R L J ys B b (fun y => hl (B y)) iρ hy).hom =
    (dependentRightUnitIso R L J xs A a (fun x => hl (A x)) iρ hx).hom.comp
      (⟨wordNativeMap f hs hy A B (fun j => α ys[j] (List.getElem_mem _)),h⟩ :
        AugHom ℙ (wordAug A xs a) (wordAug B ys b)) := by
  apply AugHom.ext
  exact rightUnit_original_native_square I A B f hs α R L J hl a b iρ hx hy

end AugmentedLift
end Lift


end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
