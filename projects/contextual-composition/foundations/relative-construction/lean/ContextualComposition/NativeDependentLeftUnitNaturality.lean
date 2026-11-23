module
public import ContextualComposition.NativeDependentUnitNaturality
@[expose] public section

/-! Left-unit naturality on the original dependent lift, including
selected empty fibres and arbitrary whole native continuation maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X : Type u} {T : Bi (coeff (C:=C))} {I : C}
section LeftLift
variable {Y : Type u} [DecidableEq Y] {xs : List X} {ys : List Y}
variable (I : C) (A : X → C) (B : Y → C)
variable (f : X → Y) (hs : ∀ x ∈ xs, f x ∈ ys)
variable (α : ∀ y ∈ ys, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A (wordFibre xs f y) ⟶ B y)

set_option backward.isDefEq.respectTransparency false in
/-- Lift the full continuation arrow at the single unit parent. -/
def leftUnitLiftInput :
    OrderedDependentMap ([PUnit.unit] : List PUnit.{u+1}) (fun _ => xs)
      ([PUnit.unit] : List PUnit.{u+1}) (fun _ => ys) (fun _ => I) (fun _ => A) (fun _ => I) (fun _ => B) where
  parent := id
  child := fun _ => f
  parent_mem := fun _ h => h
  child_mem := fun _ _ _ hx => hs _ hx
  outer := fun y hy => by
    have h : y = PUnit.unit := Subsingleton.elim _ _
    subst y
    exact (ρ_ I).hom
  inner := fun _ _ => α

set_option backward.isDefEq.respectTransparency false in
theorem leftUnitLiftInput_read {U : Type u} (s : List U) :
    (dependentWord ([PUnit.unit] : List PUnit.{u+1}) (fun _ => s)).map Prod.snd = s := by
  change (((s.map (Prod.mk PUnit.unit))) ++ []).map Prod.snd = s
  rw [List.append_nil, List.map_map]
  exact List.map_id s

set_option backward.isDefEq.respectTransparency false in
theorem leftUnitLiftInput_outerNative
    (h₀ : ([PUnit.unit] : List PUnit.{u+1}).Nodup) :
    (leftUnitLiftInput I A B f hs α).outerNative h₀ =
      Hom.ident (wordFamily (fun _ : PUnit.{u+1} => I) [PUnit.unit]) := by
  let D := leftUnitLiftInput I A B f hs α
  unfold OrderedDependentMap.outerNative
  apply wordNativeMap_ident_of_singleton h₀ (fun _ : PUnit.{u+1} => I) id _ (fun _ _ => rfl)
  intro j
  let t := ([PUnit.unit] : List PUnit.{u+1})[j]
  have e : t = PUnit.unit := Subsingleton.elim _ _
  let p (u : PUnit.{u+1}) (hu : u ∈ [PUnit.unit]) := D.outer u hu
  have h {u v : PUnit.{u+1}} (e : u = v) (hu : u ∈ [PUnit.unit]) (hv : v ∈ [PUnit.unit]) :
      HEq (p u hu) (p v hv) := by subst v; rfl
  exact (h e (List.getElem_mem _) List.mem_cons_self).trans HEq.rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem leftUnitLiftInput_cell
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lax : ∀ a : C, (rightFactor (T:=T) a).LaxBraided] (hr : ∀ a : C, SameRightGather R a)
    (y : Y) (hy : y ∈ ys) :
    HEq (origDependentCell (leftUnitLiftInput I A B f hs α) R L (PUnit.unit,y)
      ((dependentWord_mem _ _ _).mpr ⟨List.mem_cons_self,hy⟩))
      ((Lin.left L I).collect A (wordFibre xs f y) ≫ T.map (𝟙 I) (α y hy)) := by
  let D := leftUnitLiftInput I A B f hs α
  let h₀ := ((dependentWord_mem ([PUnit.unit] : List PUnit.{u+1}) (fun _ => ys) (PUnit.unit,y)).mpr ⟨List.mem_cons_self,hy⟩)
  let S := D.Slice PUnit.unit
  let i : S := ⟨PUnit.unit,List.mem_cons_self,rfl⟩
  let M := wordFibre xs f y
  let G := dependentLabels (T:=T) (fun _ : PUnit.{u+1} => I) (fun _ => A)
  let F := fold 𝒮 Zₐ G
  let g := fun (p : S) (t : X) => (p.val,t)
  let y₀ := fun _ : S => M
  let W := wordFibre (dependentWord [PUnit.unit] (fun _ => xs)) (origDepCarrier D) (PUnit.unit,y)
  let V := fun x => T.obj I (A x)
  let B₀ := T.obj I (B y)
  let p : fold 𝒮 Zₐ V M ⟶ B₀ := (Lin.left L I).collect A M ≫ T.map (𝟙 I) (α y hy)
  have hα : D.innerSliceCell i y hy = α y hy := by
    unfold OrderedDependentMap.innerSliceCell OrderedDependentMap.locInner
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hp : attachedSliceChildCell D L i y hy = p := by
    unfold attachedSliceChildCell
    rw [hα]
    rfl
  have h := origDependentCell_flatRows D R L (PUnit.unit,y) h₀
  have P₀ : ((M.map (g i)) ++ []) = W := by
    have e := dependentSlice_word_raw D (PUnit.unit,y)
    unfold dependentWord at e
    simp only [List.map_flatMap, List.map_map] at e
    change ((M.map (g i)) ++ []) = W at e
    exact e
  have hr₀ : DependentFibre.gather R (D.parentVal PUnit.unit) (B y) (D.slice PUnit.unit) ≫
      T.map (D.locOuter PUnit.unit List.mem_cons_self) (𝟙 (B y)) = (ρ_ B₀).hom := by
    have hα₀ : D.locOuter PUnit.unit List.mem_cons_self = (ρ_ I).hom := by
      unfold OrderedDependentMap.locOuter
      change eqToHom (rfl : I ⊗ Zₐ = I ⊗ Zₐ) ≫ (ρ_ I).hom = (ρ_ I).hom
      simp
    rw [hα₀]
    exact gatherRight_singleton_unit R I (B y) (hr _)
  change origDependentCell D R L (PUnit.unit,y) h₀ = eqToHom (congrArg F P₀.symm) ≫
    taggedRaggedRows G g y₀ [i] ≫
    act 𝒮 Zₐ (fun x => attachedSliceChildCell D L x y hy) [i] ≫
    DependentFibre.gather R (D.parentVal PUnit.unit) (B y) (D.slice PUnit.unit) ≫
      T.map (D.locOuter PUnit.unit List.mem_cons_self) (𝟙 (B y)) at h
  rw [h, hr₀]
  unfold taggedRaggedRows
  simp only [Category.assoc]
  let e₀ := std_fold_map G (g i) M
  let k := fun z : S => (y₀ z).map (g z)
  let F₀ := F (k i)
  let N := fold 𝒮 Zₐ V M
  let a₀ : F₀ ⟶ N := eqToHom e₀
  change HEq
    (eqToHom (congrArg F P₀.symm) ≫ rowsChart G k [i] ≫ (a₀ ⊗ₘ 𝟙 Zₐ) ≫
      ((attachedSliceChildCell D L i y hy) ⊗ₘ 𝟙 Zₐ) ≫ (ρ_ B₀).hom) p
  rw [hp]
  have ha : (a₀ ⊗ₘ 𝟙 Zₐ) ≫ (ρ_ N).hom = (ρ_ F₀).hom ≫ a₀ := by
    rw [tensorHom_id]
    exact rightUnitor_naturality a₀
  have hb : (p ⊗ₘ 𝟙 Zₐ) ≫ (ρ_ B₀).hom = (ρ_ N).hom ≫ p := by
    rw [tensorHom_id]
    exact rightUnitor_naturality p
  have hc := rowsChart_one G k i
  rw [hb, reassoc_of% ha]
  let e₁ := congrArg F (List.append_nil (k i)).symm
  let e₂ := congrArg F ((List.append_nil (k i)).symm.trans P₀)
  have he : congrArg F P₀.symm = e₂.symm.trans e₁ := Subsingleton.elim _ _
  rw [he, ← eqToHom_trans e₂.symm e₁]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  change HEq (eqToHom e₂.symm ≫ eqToHom e₀ ≫ p) p
  rw [eqToHom_trans_assoc]
  exact hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
theorem leftUnitLiftInput_native_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lax : ∀ a : C, (rightFactor (T:=T) a).LaxBraided] (hr : ∀ a : C, SameRightGather R a)
    (hy : ys.Nodup) :
    HEq
      (origDependentWordMap (leftUnitLiftInput I A B f hs α) R L
        (dependentWord_nodup (by simp) (fun _ _ => hy)))
      (wordNativeMap f hs hy (fun x => T.obj I (A x)) (fun y => T.obj I (B y))
        (fun j => (Lin.left L I).collect A (wordFibre xs f ys[j]) ≫ T.map (𝟙 I) (α ys[j] (List.getElem_mem _)))) := by
  let D := leftUnitLiftInput I A B f hs α
  let F₀ := fun x => T.obj I (A x)
  let F₁ := fun y => T.obj I (B y)
  let w₀ := dependentWord ([PUnit.unit] : List PUnit.{u+1}) (fun _ => xs)
  let w₁ := dependentWord ([PUnit.unit] : List PUnit.{u+1}) (fun _ => ys)
  let φ := fun j : Fin w₁.length => origDependentCell D R L w₁[j] (List.getElem_mem _)
  let ψ (j : Fin ys.length) := (Lin.left L I).collect A (wordFibre xs f ys[j]) ≫
    T.map (𝟙 I) (α ys[j] (List.getElem_mem _))
  have ex : w₀.map Prod.snd = xs := leftUnitLiftInput_read xs
  have ey : w₁.map Prod.snd = ys := leftUnitLiftInput_read ys
  change HEq (wordNativeMap (origDepCarrier D) (origDepCarrier_support D) _
    (F₀ ∘ Prod.snd) (F₁ ∘ Prod.snd) φ) (wordNativeMap f hs hy F₀ F₁ ψ)
  apply readWordNativeMap_heq F₀ F₁ Prod.snd Prod.snd (origDepCarrier D) f
    (origDepCarrier_support D) hs _ hy ex ey (fun _ _ => rfl) φ ψ
  intro j
  let k := Fin.cast ((List.length_map (Prod.snd : PUnit.{u+1} × Y → Y)).symm.trans (congrArg List.length ey)) j
  let y := w₁[j].2
  have e : y = ys[k] := retag_word_get Prod.snd w₁ ey j
  have i : w₁[j] = (PUnit.unit,y) := Prod.ext (Subsingleton.elim _ _) rfl
  let w (t : PUnit.{u+1} × Y) (h : t ∈ w₁) := origDependentCell D R L t h
  have h {a b : PUnit.{u+1} × Y} (e : a = b) (ha : a ∈ w₁) (hb : b ∈ w₁) :
      HEq (w a ha) (w b hb) := by subst b; rfl
  exact (h (i.trans (congrArg (fun c => (PUnit.unit,c)) e)) (List.getElem_mem _)
      ((dependentWord_mem _ _ _).mpr ⟨List.mem_cons_self,List.getElem_mem _⟩)).trans
    (leftUnitLiftInput_cell I A B f hs α R L hr ys[k] (List.getElem_mem _))



set_option backward.isDefEq.respectTransparency false in
theorem dependentLeftUnitIso_pointwise_heq {Z : Type u}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
    (xs : List Z) (V : Z → C) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (hI : depLeftUnitCell R J P I = J.ρ I) (ι : ∀ a, IsIso (depLeftUnitCell R J P a))
    (hn : xs.Nodup) :
    HEq (dependentLeftUnitIso R L J P Q xs V ε hI ι hn).hom.native
      (wordPointwise xs (fun x => depLeftUnitCell R J P (V x))) := by
  unfold dependentLeftUnitIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (wordAugIso_ident_pointwise _ _ _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
/-- Native naturality of the left unit. An arbitrary input map occurs
as the continuation under the genuine identity singleton parent. -/
theorem leftUnit_original_native_square
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (J : UnitCompat R I)
    (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
    [lax : ∀ a : C, (rightFactor (T:=T) a).LaxBraided] (hr : ∀ a : C, SameRightGather R a)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (hI : depLeftUnitCell R J P I = J.ρ I) (ι : ∀ c, IsIso (depLeftUnitCell R J P c))
    (hx : xs.Nodup) (hy : ys.Nodup) :
    (origDependentWordMap (leftUnitLiftInput I A B f hs α) R L
      (dependentWord_nodup (by simp) (fun _ _ => hy))).comp
      (dependentLeftUnitIso R L J P Q ys B b hI ι hy).hom.native =
    (dependentLeftUnitIso R L J P Q xs A a hI ι hx).hom.native.comp
      (wordNativeMap f hs hy A B (fun y => α ys[y] (List.getElem_mem _))) := by
  let F₀ := fun x => T.obj I (A x)
  let F₁ := fun y => T.obj I (B y)
  let p (y : Y) (hm : y ∈ ys) := (Lin.left L I).collect A (wordFibre xs f y) ≫ T.map (𝟙 I) (α y hm)
  let e₀ (x : X) : F₀ x ≅ A x := by
    let _ := ι (A x)
    exact asIso (depLeftUnitCell R J P (A x))
  let e₁ (y : Y) : F₁ y ≅ B y := by
    let _ := ι (B y)
    exact asIso (depLeftUnitCell R J P (B y))
  let g := origDependentWordMap (leftUnitLiftInput I A B f hs α) R L
    (dependentWord_nodup (by simp) (fun _ _ => hy))
  let k := wordNativeMap f hs hy F₀ F₁ (fun j => p ys[j] (List.getElem_mem _))
  let q := wordNativeMap f hs hy A B (fun j => α ys[j] (List.getElem_mem _))
  let u := (dependentLeftUnitIso R L J P Q xs A a hI ι hx).hom.native
  let v := (dependentLeftUnitIso R L J P Q ys B b hI ι hy).hom.native
  have h := wordNativeMap_identChart_square f hs hx hy F₀ A F₁ B e₀ e₁ p α
    (fun y hy => by
      unfold p
      rw [Category.assoc]
      exact leftUnit_whole_cell R L J P Q A (wordFibre xs f y) (α y hy))
  rw [wordReindex_ident_pointwise, wordReindex_ident_pointwise] at h
  have ex := wordFamily_read_eq F₀ Prod.snd _ xs (leftUnitLiftInput_read xs)
  have ey := wordFamily_read_eq F₁ Prod.snd _ ys (leftUnitLiftInput_read ys)
  have hg : HEq g k := leftUnitLiftInput_native_heq I A B f hs α R L hr hy
  have hu := dependentLeftUnitIso_pointwise_heq I R L J P Q xs A a hI ι hx
  have hv := dependentLeftUnitIso_pointwise_heq I R L J P Q ys B b hI ι hy
  change g.comp v = u.comp q
  exact eq_of_heq ((nativeHom_comp_heq g v k _ ex ey rfl hg hv).trans
    ((heq_of_eq h).trans (nativeHom_comp_heq u q _ q ex rfl rfl hu HEq.rfl).symm))


section AugmentedLift
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

set_option backward.isDefEq.respectTransparency false in
noncomputable def leftUnitLiftAugMap :
    AugHom ℙ
      (dependentWordAug R L J ([PUnit.unit] : List PUnit.{u+1}) (fun _ => xs)
        (fun _ => I) (fun _ => A) (indexedAugmentation (fun _ => a)) (ρ_ I).hom)
      (dependentWordAug R L J ([PUnit.unit] : List PUnit.{u+1}) (fun _ => ys)
        (fun _ => I) (fun _ => B) (indexedAugmentation (fun _ => b)) (ρ_ I).hom) := by
  let D := leftUnitLiftInput I A B f hs α
  have p : D.Preserves (by simp) (fun _ _ => hy) (fun _ => a) (fun _ => b)
      (ρ_ I).hom (ρ_ I).hom := by
    refine ⟨?_, fun _ _ => h⟩
    rw [leftUnitLiftInput_outerNative I A B f hs α]
    exact Hom.ident_comp _
  exact D.accumulateAug R L J N NL hl (by simp) (by simp) (fun _ _ => hx) (fun _ _ => hy) p

set_option backward.isDefEq.respectTransparency false in
theorem leftUnit_original_augmented_square
    (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
    [rlax : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c)
    (hI : depLeftUnitCell R J P I = J.ρ I) (ι : ∀ c, IsIso (depLeftUnitCell R J P c)) :
    (leftUnitLiftAugMap I A B f hs α R L J N NL hl a b hx hy h).comp
      (dependentLeftUnitIso R L J P Q ys B b hI ι hy).hom =
    (dependentLeftUnitIso R L J P Q xs A a hI ι hx).hom.comp
      (⟨wordNativeMap f hs hy A B (fun j => α ys[j] (List.getElem_mem _)),h⟩ :
        AugHom ℙ (wordAug A xs a) (wordAug B ys b)) := by
  apply AugHom.ext
  exact leftUnit_original_native_square I A B f hs α R L J P Q hr a b hI ι hx hy

end AugmentedLift
end LeftLift

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
