module
public import ContextualComposition.NativeBinaryAugmentedNaturality
@[expose] public section

/-! The identity calculation is on the literal one-leaf dependent chart,
including both right-fold nullary tails. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}

set_option backward.isDefEq.respectTransparency false in
theorem gatherLeft_singleton_unit
    (L : LeftGather 𝒮 T Zₐ) (a b : C)
    [(leftFactor T a).LaxBraided] (_h : SameLeftGather T a L) :
    gatherLeft L a [b] ≫ T.map (𝟙 a) (ρ_ b).hom = (ρ_ (T.obj a b)).hom := by
  have k := collect_singleton (leftFactor T a) id b
  rw [leftFactor_sameCollect T a L _h] at k
  change (Lin.left L a).collect id [b] ≫ T.map (𝟙 a) (ρ_ b).hom = _ at k
  change (Lin.left L a).collect id [b] ≫ T.map (𝟙 a) (ρ_ b).hom = _
  exact k

set_option backward.isDefEq.respectTransparency false in
theorem gatherRight_singleton_unit
    (R : Gather 𝒮 T Zₐ) (a b : C)
    [(rightFactor (T:=T) b).LaxBraided] (_h : SameRightGather R b) :
    DependentFibre.gather R id b [a] ≫ T.map (ρ_ a).hom (𝟙 b) = (ρ_ (T.obj a b)).hom := by
  have k := collect_singleton (rightFactor (T:=T) b) id a
  rw [rightFactor_sameCollect R _h] at k
  exact k

set_option backward.isDefEq.respectTransparency false in
theorem dependent_singleton_chart_unit
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) (a b : C)
    [(leftFactor T a).LaxBraided] [(rightFactor (T:=T) b).LaxBraided]
    (_hl : SameLeftGather T a L) (_hr : SameRightGather R b) :
    (ρ_ (T.obj a b ⊗ Zₐ)).inv ≫
      dep R (fun _ : PUnit.{u+1} => a) (indexInput (fun _ _ : PUnit.{u+1} => b) (fun _ => [PUnit.unit])) L [PUnit.unit]
        (fun _ => (ρ_ b).hom) (ρ_ a).hom =
      (ρ_ (T.obj a b)).hom := by
  have hl := gatherLeft_singleton_unit L a b _hl
  have hr := gatherRight_singleton_unit R a b _hr
  let p := gatherLeft L a [b] ≫ T.map (𝟙 a) (ρ_ b).hom
  change (ρ_ (T.obj a b ⊗ Zₐ)).inv ≫
    (p ⊗ₘ 𝟙 Zₐ) ≫ DependentFibre.gather R id b [a] ≫ T.map (ρ_ a).hom (𝟙 b) = _
  have h : (ρ_ (T.obj a b ⊗ Zₐ)).inv ≫ (p ⊗ₘ 𝟙 Zₐ) =
      p ≫ (ρ_ (T.obj a b)).inv := by
    rw [tensorHom_id]
    exact (rightUnitor_inv_naturality p).symm
  change p = (ρ_ (T.obj a b)).hom at hl
  rw [reassoc_of% h, hl, Iso.hom_inv_id_assoc, hr]


set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_singleLeaf_row {X : Type u} (A : X → C) (a : X) :
    compressGrid A (GridExpr.bin (.leaf a) .zero) = 𝟙 (A a ⊗ Zₐ) := by
  change join additiveStructure A [a] [] ≫ ((ρ_ (A a)).hom ⊗ₘ 𝟙 Zₐ) = _
  have h : join additiveStructure A [a] [] = (ρ_ (A a ⊗ Zₐ)).inv := by
    have k := std_join_right_unit A [a]
    change 𝟙 _ ≫ join additiveStructure A [a] [] = _ at k
    rw [Category.id_comp] at k
    exact k
  rw [h]
  change (ρ_ (A a ⊗ Zₐ)).inv ≫ ((ρ_ (A a)).hom ⊗ₘ 𝟙 Zₐ) = 𝟙 _
  rw [tensorHom_id, ← rightUnitor_inv_naturality, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
theorem compressGrid_singleLeaf_nested {X : Type u} (A : X → C) (a : X) :
    compressGrid A (GridExpr.bin (.bin (.leaf a) .zero) .zero) =
      (ρ_ (A a ⊗ Zₐ)).inv := by
  change join additiveStructure A [a] [] ≫
    (compressGrid A (.bin (.leaf a) .zero) ⊗ₘ 𝟙 Zₐ) = _
  rw [compressGrid_singleLeaf_row]
  let j : A a ⊗ Zₐ ⟶ (A a ⊗ Zₐ) ⊗ Zₐ := join additiveStructure A [a] []
  change j ≫ (𝟙 (A a ⊗ Zₐ) ⊗ₘ 𝟙 Zₐ) = _
  rw [tensorHom_id, id_whiskerRight, Category.comp_id]
  have k := std_join_right_unit A [a]
  change 𝟙 _ ≫ join additiveStructure A [a] [] = _ at k
  rw [Category.id_comp] at k
  exact k


theorem wordFibre_identity_singleton {X : Type u} [DecidableEq X] {xs : List X}
    (n : xs.Nodup) {x : X} (h : x ∈ xs) :
    wordFibre xs id x = [x] := by
  unfold wordFibre
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
      simpa only [List.filter_cons, id_eq, e, decide_false, Bool.false_eq_true, ite_false]
        using ih (List.nodup_cons.mp n).2 hh

set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_ident_of_singleton {X : Type u} [DecidableEq X]
    {xs : List X} (hn : xs.Nodup) (A : X → C) (f : X → X)
    (hs : ∀ x ∈ xs, f x ∈ xs) (e : ∀ x ∈ xs, f x = x)
    (p : ∀ i : Fin xs.length, fold 𝒮 Zₐ A (wordFibre xs f xs[i]) ⟶ A xs[i])
    (k : ∀ i : Fin xs.length, HEq (p i) (ρ_ (A xs[i])).hom) :
    wordNativeMap f hs hn A A p = Hom.ident (wordFamily A xs) := by
  have d : wordCarrier f hs hn = id := by
    funext i
    exact (wordCarrier_eq_iff f hs hn i i).mpr (e _ (List.getElem_mem _))
  apply native_hom_ext d
  intro i
  let c := wordCarrier_fibre_pin f hs hn A i
  let O := (wordFamily A xs).val
  let Z := standardPushObj (wordCarrier f hs hn) O i
  let s := congrArg (fun k => standardPushObj k O i) d
  let r : standardPushObj id O i = A xs[i] ⊗ Zₐ :=
    congrArg (fold 𝒮 Zₐ O) (fibreList_id i)
  have fibre : wordFibre xs f xs[i] = [xs[i]] := by
    have m : wordFibre xs f xs[i] = wordFibre xs id xs[i] := by
      apply List.filter_congr
      intro x hx
      simp only [e x hx, id_eq]
    exact m.trans (wordFibre_identity_singleton hn (List.getElem_mem _))
  let q := congrArg (fold 𝒮 Zₐ A) fibre
  have h : p i = eqToHom q ≫ (ρ_ (A xs[i])).hom := by
    have H := heq_paste q rfl (k i)
    simp only [eqToHom_refl, Category.comp_id] at H
    exact H
  change eqToHom c ≫ p i = eqToHom s ≫ eqToHom r ≫ (ρ_ (A xs[i])).hom
  rw [h, reassoc_of% eqToHom_trans c q, reassoc_of% eqToHom_trans s r]


set_option backward.isDefEq.respectTransparency false in
theorem gatherLeft_singleton_heq
    (L : LeftGather 𝒮 T Zₐ) (a b : C) (ls : List C) (e : ls = [b])
    [(leftFactor T a).LaxBraided] (_h : SameLeftGather T a L)
    (q : fold 𝒮 Zₐ id ls ⟶ b) (hq : HEq q (ρ_ b).hom) :
    HEq (gatherLeft L a ls ≫ T.map (𝟙 a) q) (ρ_ (T.obj a b)).hom := by
  subst ls
  have d : q = (ρ_ b).hom := eq_of_heq hq
  subst q
  exact heq_of_eq (gatherLeft_singleton_unit L a b _h)

set_option backward.isDefEq.respectTransparency false in
theorem dependentLocal_singleton_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {X U : Type u} (V : X → C) (B : X → U → C)
    (xs : List X) (us : X → List U) (x : X) (t : U)
    (_ex : xs = [x]) (eu : us x = [t])
    [(leftFactor T (V x)).LaxBraided] [(rightFactor (T:=T) (B x t)).LaxBraided]
    (_hl : SameLeftGather T (V x) L) (_hr : SameRightGather R (B x t))
    (β : ∀ j, inner (S:=𝒮) (Z:=Zₐ) (indexInput B us) j ⟶ B x t)
    (α : fold 𝒮 Zₐ V xs ⟶ V x)
    (ha : HEq α (ρ_ (V x)).hom) (hb : HEq (β x) (ρ_ (B x t)).hom) :
    HEq (compressGrid (dependentLabels (T:=T) V B) (dependentExpr xs us) ≫
      eqToHom (dependentExpr_eval V B xs us) ≫ dep R V (indexInput B us) L xs β α)
      (ρ_ (T.obj (V x) (B x t))).hom := by
  subst xs
  let a := V x
  let b := B x t
  let G := dependentLabels (T:=T) V B
  let sin : GridExpr (X × U) := .bin (.bin (.leaf (x,t)) .zero) .zero
  let E := dependentExpr [x] us
  have ee : E = sin := by
    change GridExpr.bin (GridExpr.over (fun t => GridExpr.leaf (x,t)) (us x)) .zero = sin
    rw [eu]
    rfl
  have ec : HEq (compressGrid G E) (ρ_ (T.obj a b ⊗ Zₐ)).inv := by
    have hh {e₁ e₂ : GridExpr (X × U)} (e : e₁ = e₂) :
        HEq (compressGrid G e₁) (compressGrid G e₂) := by cases e; rfl
    exact (hh ee).trans (heq_of_eq (compressGrid_singleLeaf_nested G (x,t)))
  have hd : α = (ρ_ a).hom := eq_of_heq ha
  let ls := (indexInput B us).terms x
  let c := row V (indexInput B us) L β x
  have es : ls = [b] := by change (us x).map (B x) = _; rw [eu]; rfl
  have hc : HEq c (ρ_ (T.obj a b)).hom := gatherLeft_singleton_heq L a b ls es _hl (β x) hb
  let h : fold 𝒮 Zₐ (T.obj a) ls = T.obj a b ⊗ Zₐ := congrArg (fold 𝒮 Zₐ (T.obj a)) es
  have hd₁ : HEq (dep R V (indexInput B us) L [x] β α)
      (((ρ_ (T.obj a b)).hom ⊗ₘ 𝟙 Zₐ) ≫
        DependentFibre.gather R id b [a] ≫ T.map (ρ_ a).hom (𝟙 b)) := by
    change HEq ((c ⊗ₘ 𝟙 Zₐ) ≫ DependentFibre.gather R id b [a] ≫ T.map α (𝟙 b)) _
    rw [hd]
    exact structural_seq_heq (K:=coeff (C:=C)) (congrArg (fun q => q ⊗ Zₐ) h) rfl rfl
      (structural_map_heq (S:=𝒮) h rfl rfl rfl hc HEq.rfl) HEq.rfl
  let e₀ := congrArg (fold 𝒮 Zₐ G) (congrArg GridExpr.leaves ee)
  let e₁ := congrArg (fun q => q ⊗ Zₐ) h
  let ce := eqToHom (dependentExpr_eval (T:=T) V B [x] us)
  have hec : HEq (compressGrid G E ≫ ce) (ρ_ (T.obj a b ⊗ Zₐ)).inv :=
    (hom_target_pin_heq _ _).trans ec
  have e' := structural_seq_heq (K:=coeff (C:=C)) e₀ e₁ rfl hec hd₁
  have u : (ρ_ (T.obj a b ⊗ Zₐ)).inv ≫
      ((ρ_ (T.obj a b)).hom ⊗ₘ 𝟙 Zₐ) ≫ DependentFibre.gather R id b [a] ≫ T.map (ρ_ a).hom (𝟙 b) =
      (ρ_ (T.obj a b)).hom := by
    rw [tensorHom_id, ← rightUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc,
      gatherRight_singleton_unit R a b _hr]
  exact (heq_of_eq (Category.assoc _ _ _).symm).trans (e'.trans (heq_of_eq u))


section OrderedIdentity
variable {X U : Type u} [DecidableEq X] [DecidableEq U]
variable (xs : List X) (us : X → List U) (V : X → C) (W : X → U → C)
variable (hn : xs.Nodup) (hc : ∀ x ∈ xs, (us x).Nodup)

def OrderedDependentMap.identity :
    OrderedDependentMap xs us xs us V W V W where
  parent := id
  child := fun _ => id
  parent_mem := fun _ p => p
  child_mem := fun _ _ _ p => p
  outer := fun j h =>
    eqToHom (congrArg (fold 𝒮 Zₐ V) (wordFibre_identity_singleton hn h)) ≫ (ρ_ (V j)).hom
  inner := fun x hx t ht =>
    eqToHom (congrArg (fold 𝒮 Zₐ (W x)) (wordFibre_identity_singleton (hc x hx) ht)) ≫ (ρ_ (W x t)).hom

set_option backward.isDefEq.respectTransparency false in
theorem dependentIdentity_slice (x : X) (hx : x ∈ xs) :
    let D := OrderedDependentMap.identity xs us V W hn hc
    D.slice x = [⟨x,hx,rfl⟩] := by
  intro D
  let y : D.Slice x := ⟨x,hx,rfl⟩
  have h : (D.slice x).map Subtype.val = [x] :=
    (sliceWord_map xs D.parent x).trans (wordFibre_identity_singleton hn hx)
  generalize D.slice x = s at h ⊢
  cases s with
  | nil => simp at h
  | cons a l =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at h
    rcases h with ⟨ha,rfl⟩
    exact congrArg (fun p : D.Slice x => [p]) (Subtype.ext ha)

set_option backward.isDefEq.respectTransparency false in
theorem dependentIdentity_cell_heq
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    (p : X × U) (hp : p ∈ dependentWord xs us) :
    let D := OrderedDependentMap.identity xs us V W hn hc
    HEq (origDependentCell D R L p hp) (ρ_ (dependentLabels (T:=T) V W p)).hom := by
  intro D
  let k := (dependentWord_mem xs us p).mp hp
  let x : D.Slice p.1 := ⟨p.1,k.1,rfl⟩
  let y := p.2
  have e : D.slice p.1 = [x] := dependentIdentity_slice xs us V W hn hc p.1 k.1
  have d : D.terms p.1 p.2 x = [y] := wordFibre_identity_singleton (hc p.1 k.1) k.2
  let a := D.parentVal p.1 x
  let b := D.childVal p.1 x y
  let _ : (leftFactor T a).LaxBraided := lF a
  let _ : (rightFactor (T:=T) b).LaxBraided := rF b
  have ar : HEq (D.locOuter p.1 k.1) (ρ_ a).hom := by
    change HEq (eqToHom _ ≫ (eqToHom _ ≫ (ρ_ a).hom)) _
    exact (hom_source_pin_heq _ _).trans (hom_source_pin_heq _ _)
  have br : HEq (D.locInner p.1 p.2 k.2 x) (ρ_ b).hom := by
    change HEq (eqToHom _ ≫ (eqToHom _ ≫ (ρ_ b).hom) ≫ eqToHom _) _
    exact (hom_source_pin_heq _ _).trans ((hom_target_pin_heq _ _).trans (hom_source_pin_heq _ _))
  have u := dependentLocal_singleton_heq R L (D.parentVal p.1) (D.childVal p.1)
    (D.slice p.1) (D.terms p.1 p.2) x y e d (_hl a) (_hr b)
    (D.locInner p.1 p.2 k.2) (D.locOuter p.1 k.1) ar br
  unfold origDependentCell localCellToGlobal
  exact (hom_source_pin_heq _ _).trans u

set_option backward.isDefEq.respectTransparency false in
theorem origDependentWordMap_ident
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b) :
    origDependentWordMap (OrderedDependentMap.identity xs us V W hn hc) R L (dependentWord_nodup hn hc) =
      Hom.ident (wordFamily (dependentLabels (T:=T) V W) (dependentWord xs us)) := by
  unfold origDependentWordMap
  apply wordNativeMap_ident_of_singleton
  · intro p _
    rcases p with ⟨a,b⟩
    rfl
  · intro i
    exact dependentIdentity_cell_heq xs us V W hn hc R L _hl _hr _ _


set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.identity_outer :
    (OrderedDependentMap.identity xs us V W hn hc).outerNative hn =
      Hom.ident (wordFamily V xs) := by
  unfold OrderedDependentMap.outerNative
  apply wordNativeMap_ident_of_singleton hn V
  · intro a _
    rfl
  · intro i
    exact hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.identity_inner (x : X) (hx : x ∈ xs) :
    (OrderedDependentMap.identity xs us V W hn hc).innerNative x hx (hc x hx) =
      Hom.ident (wordFamily (W x) (us x)) := by
  unfold OrderedDependentMap.innerNative
  apply wordNativeMap_ident_of_singleton
  · intro a _
    rfl
  · intro i
    exact hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.identity_preserves {I : C}
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I) (ε : fold 𝒮 Zₐ V xs ⟶ I) :
    (OrderedDependentMap.identity xs us V W hn hc).Preserves hn hc δ δ ε ε where
  outer := by rw [OrderedDependentMap.identity_outer, Hom.ident_comp]
  inner x hx := by rw [OrderedDependentMap.identity_inner, Hom.ident_comp]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem origDependentWordAugMap_ident
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (_hl : ∀ a : C, SameLeftGather T a L) (_hr : ∀ b : C, SameRightGather R b)
    {I : C} (J : UnitCompat R I)
    (δ : ∀ x, fold 𝒮 Zₐ (W x) (us x) ⟶ I) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    (p : AugHom ℙ (dependentWordAug R L J xs us V W (indexedAugmentation δ) ε)
      (dependentWordAug R L J xs us V W (indexedAugmentation δ) ε))
    (hp : p.native = origDependentWordMap (OrderedDependentMap.identity xs us V W hn hc) R L
      (dependentWord_nodup hn hc)) :
    p = AugHom.ident (dependentWordAug R L J xs us V W (indexedAugmentation δ) ε) := by
  apply AugHom.ext
  rw [hp]
  exact origDependentWordMap_ident xs us V W hn hc R L _hl _hr

end OrderedIdentity
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
