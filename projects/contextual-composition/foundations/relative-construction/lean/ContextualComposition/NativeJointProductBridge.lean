module
public import ContextualComposition.NativeJointProductCharts
@[expose] public section

/-! Identify the independently constructed product input after unary accumulation with the literal binary joint arrow. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

section NativeInput
def OrderedDependentMap.pairSlice (t : X' × Y') (p : D.Slice t.1 × E.Slice t.2) :
    (D.independentProduct E R L).Slice t :=
  ⟨(p.1.val,p.2.val),(mem_ordered_product xs ys _).mpr ⟨p.1.property.1,p.2.property.1⟩,
    Prod.ext p.1.property.2 p.2.property.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairSlice_word (t : X' × Y') :
    ((D.slice t.1).product (E.slice t.2)).map (D.pairSlice E R L t) =
      (D.independentProduct E R L).slice t := by
  let p := D.independentProduct E R L
  have i : Function.Injective (Subtype.val : p.Slice t → X × Y) := fun _ _ h => Subtype.ext h
  apply (List.map_inj_right (fun _ _ h => i h)).mp
  rw [List.map_map, sliceWord_map]
  change (((D.slice t.1).product (E.slice t.2)).map
    (Prod.map (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2 => y.val))) = _
  rw [map_product_word, sliceWord_map, sliceWord_map]
  exact (product_word_fibre xs ys D.parent E.parent t).symm

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairSlice_terms (t : X' × Y') (w : U' × W') (p : D.Slice t.1 × E.Slice t.2) :
    (D.independentProduct E R L).terms t w (D.pairSlice E R L t p) =
      (D.terms t.1 w.1 p.1).product (E.terms t.2 w.2 p.2) :=
  product_word_fibre (us p.1.val) (vs p.2.val) (D.child p.1.val) (E.child p.2.val) w

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.locOuter_heq_raw (t : X') (h : t ∈ xs') :
    HEq (D.locOuter t h) (D.outer t h) :=
  hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairLocOuter_heq (t : X' × Y') (h : t ∈ xs'.product ys') :
    let a := D.slice t.1
    let b := E.slice t.2
    let h' := (mem_ordered_product xs' ys' t).mp h
    HEq ((D.independentProduct E R L).locOuter t h)
      (rectWordChart (crossLabel T (D.parentVal t.1) (E.parentVal t.2)) a b ≫
        independentCell R L (D.parentVal t.1) (E.parentVal t.2) a b
          (D.locOuter t.1 h'.1) (E.locOuter t.2 h'.2)) := by
  intro a b h'
  let p := D.independentProduct E R L
  have h₀ : HEq (p.locOuter t h) (p.outer t h) := p.locOuter_heq_raw t h
  have h₁ : HEq (p.outer t h)
      (rectWordChart (crossLabel T V P) (parentFibreA xs D.parent t.1) (parentFibreA ys E.parent t.2) ≫
        independentCell R L V P (parentFibreA xs D.parent t.1) (parentFibreA ys E.parent t.2)
          (D.outer t.1 h'.1) (E.outer t.2 h'.2)) :=
    hom_source_pin_heq _ _
  have h₃ {aa' : List X} {bb' : List Y}
      (ea : a.map Subtype.val = aa') (eb : b.map Subtype.val = bb')
      (α : fold 𝒮 Zₐ V aa' ⟶ V' t.1) (γ : fold 𝒮 Zₐ P bb' ⟶ P' t.2)
      (ha : HEq (D.locOuter t.1 h'.1) α) (hb : HEq (E.locOuter t.2 h'.2) γ) :
      HEq
        (rectWordChart (crossLabel T (D.parentVal t.1) (E.parentVal t.2)) a b ≫
          independentCell R L (D.parentVal t.1) (E.parentVal t.2) a b
            (D.locOuter t.1 h'.1) (E.locOuter t.2 h'.2))
        (rectWordChart (crossLabel T V P) aa' bb' ≫ independentCell R L V P aa' bb' α γ) := by
    subst aa'
    subst bb'
    have z := rectangleCell_map_heq R L V P
      (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2 => y.val) a b rfl rfl ha hb
    simp only [independentCell, coeff]
    exact z
  exact h₀.trans (h₁.trans ((h₃ (sliceWord_map _ _ _) (sliceWord_map _ _ _) _ _
      (D.locOuter_heq_raw _ _) (E.locOuter_heq_raw _ _)).symm))

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.innerSliceCell_eq_raw (x : X) (hx : x ∈ xs) (t : U')
    (ht : t ∈ us' (D.parent x)) :
    D.innerSliceCell (⟨x,hx,rfl⟩ : D.Slice (D.parent x)) t ht = D.inner x hx t ht := by
  unfold OrderedDependentMap.innerSliceCell OrderedDependentMap.locInner
  rw [← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairLocInner_heq
    (t : X' × Y') (w : U' × W') (h : w ∈ crossChildWord us' vs' t)
    (x : D.Slice t.1 × E.Slice t.2) :
    let h' := (mem_ordered_product (us' t.1) (vs' t.2) w).mp h
    HEq ((D.independentProduct E R L).innerSliceCell (D.pairSlice E R L t x) w h)
      (jointIndexedChildCell R L (D.terms t.1 w.1) (E.terms t.2 w.2)
        (D.childVal t.1) (E.childVal t.2) (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2) x) := by
  rcases t with ⟨j,k⟩
  rcases x with ⟨⟨x,hx,ex⟩,⟨y,hy,ey⟩⟩
  dsimp only at ex ey
  subst j
  subst k
  intro h'
  let p := D.independentProduct E R L
  let xx : D.Slice (D.parent x) := ⟨x,hx,rfl⟩
  let yy : E.Slice (E.parent y) := ⟨y,hy,rfl⟩
  have r : p.innerSliceCell (D.pairSlice E R L (p.parent (x,y)) (xx,yy)) w h =
      p.inner (x,y) ((mem_ordered_product xs ys _).mpr ⟨hx,hy⟩) w h := by
    exact p.innerSliceCell_eq_raw _ _ _ _
  change HEq (p.innerSliceCell (D.pairSlice E R L (p.parent (x,y)) (xx,yy)) w h) _
  rw [r]
  have hr := D.innerSliceCell_eq_raw x hx w.1 h'.1
  have hr' := E.innerSliceCell_eq_raw y hy w.2 h'.2
  change
    HEq
      (eqToHom (congrArg (fold 𝒮 Zₐ (crossLabel T (A x) (B y)))
        (product_word_fibre (us x) (vs y) (D.child x) (E.child y) w)) ≫
        rectWordChart (crossLabel T (A x) (B y)) (D.terms (D.parent x) w.1 xx) (E.terms (E.parent y) w.2 yy) ≫
        independentCell R L (A x) (B y) _ _ (D.inner x hx w.1 h'.1) (E.inner y hy w.2 h'.2))
      (rectWordChart (crossLabel T (A x) (B y)) (D.terms (D.parent x) w.1 xx) (E.terms (E.parent y) w.2 yy) ≫
        independentCell R L (A x) (B y) _ _
          (D.innerSliceCell xx w.1 h'.1) (E.innerSliceCell yy w.2 h'.2))
  rw [hr, hr']
  exact hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairSlice_chart (t : X' × Y') (w : U' × W') :
    let p := D.independentProduct E R L
    let G := dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B)
    let K := jointLeafLabels (T:=T) V P A B
    let ps := (D.slice t.1).product (E.slice t.2)
    let q := fun x : D.Slice t.1 × E.Slice t.2 => (x.1.val,x.2.val)
    let cs := crossChildWord (D.terms t.1 w.1) (E.terms t.2 w.2)
    HEq (taggedRaggedRows G (fun x : p.Slice t => Prod.mk x.val) (p.terms t w) (p.slice t))
      (taggedRaggedRows K (jointInnerTag ∘ q) cs ps) := by
  intro p G K ps q cs
  let f := D.pairSlice E R L t
  let g := fun (x : p.Slice t) (u : U × W) => (x.val,u)
  let L' := p.terms t w
  have a := taggedRaggedRows_index_heq G g L' f ps
  have h : ∀ x, (L' ∘ f) x = cs x := D.pairSlice_terms E R L t w
  have b := taggedRaggedRows_lists_heq G (g ∘ f) h ps
  have c := taggedRaggedRows_tag_heq K jointPairRetag (g ∘ f) cs ps
  rw [← D.pairSlice_word E R L t]
  exact a.trans (b.trans c)

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairSlice_chart_local (t : X' × Y') (w : U' × W') :
    let p := D.independentProduct E R L
    let G := dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B)
    let K := jointLeafLabels (T:=T) (D.parentVal t.1) (E.parentVal t.2) (D.childVal t.1) (E.childVal t.2)
    let ps := (D.slice t.1).product (E.slice t.2)
    let cs := crossChildWord (D.terms t.1 w.1) (E.terms t.2 w.2)
    HEq (taggedRaggedRows G (fun x : p.Slice t => Prod.mk x.val) (p.terms t w) (p.slice t))
      (taggedRaggedRows K jointInnerTag cs ps) := by
  intro p G K ps cs
  let H := jointLeafLabels (T:=T) V P A B
  let f := quadOuterRelabel (U:=U) (W:=W) (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2 => y.val)
  exact (D.pairSlice_chart E R L t w).trans (taggedRaggedRows_tag_heq H f jointInnerTag cs ps).symm

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairAttachedChild_heq
    (t : X' × Y') (w : U' × W') (h : w ∈ crossChildWord us' vs' t)
    (x : D.Slice t.1 × E.Slice t.2) :
    let ps := D.pairSlice E R L t x
    let h' := (mem_ordered_product (us' t.1) (vs' t.2) w).mp h
    let cs := crossChildWord (D.terms t.1 w.1) (E.terms t.2 w.2)
    let K := crossChildLabel T (D.childVal t.1) (E.childVal t.2)
    let H := crossLabel T (D.parentVal t.1) (E.parentVal t.2)
    HEq (attachedSliceChildCell (D.independentProduct E R L) L ps w h)
      ((Lin.left L (H x)).collect (K x) (cs x) ≫ T.map (𝟙 (H x))
        (jointIndexedChildCell R L (D.terms t.1 w.1) (E.terms t.2 w.2)
          (D.childVal t.1) (E.childVal t.2) (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2) x)) := by
  intro ps h' cs K H
  let p := D.independentProduct E R L
  let r := D.pairSlice_terms E R L t w x
  let k := H x
  let q := (Lin.left L k)
  let a := congrArg (fold 𝒮 Zₐ (K x)) r
  let b := congrArg (fold 𝒮 Zₐ (fun z => T.obj k (K x z))) r
  have h₁ : HEq (q.collect (K x) (p.terms t w ps)) (q.collect (K x) (cs x)) := by
    have l {xs ys : List (U × W)} (e : xs = ys) :
      HEq (q.collect (K x) xs) (q.collect (K x) ys) := by cases e; rfl
    exact l r
  have h₂ := D.pairLocInner_heq E R L t w h x
  exact structural_seq_heq (K:=coeff (C:=C)) b (congrArg (T.obj k) a)
    (rfl : T.obj k (T.obj (A' t.1 w.1) (B' t.2 w.2)) = _) h₁
    (biMap_heq (T:=T) (rfl : k = k) rfl a rfl (show HEq (𝟙 k) (𝟙 k) from HEq.rfl) h₂)

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.pairSlice_outputSchedule
    (t : X' × Y') (w : U' × W') (ha : t ∈ xs'.product ys') (hb : w ∈ crossChildWord us' vs' t) :
    let p := D.independentProduct E R L
    let s := p.slice t
    let ps := (D.slice t.1).product (E.slice t.2)
    let H := crossLabel T (D.parentVal t.1) (E.parentVal t.2)
    let h := (mem_ordered_product xs' ys' t).mp ha
    let h' := (mem_ordered_product (us' t.1) (vs' t.2) w).mp hb
    let cs := crossChildWord (D.terms t.1 w.1) (E.terms t.2 w.2)
    let K := crossChildLabel T (D.childVal t.1) (E.childVal t.2)
    let k := T.obj (A' t.1 w.1) (B' t.2 w.2)
    let g := fun x => (Lin.left L (H x)).collect (K x) (cs x) ≫ T.map (𝟙 (H x))
        (jointIndexedChildCell R L (D.terms t.1 w.1) (E.terms t.2 w.2)
          (D.childVal t.1) (E.childVal t.2) (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2) x)
    HEq
      (act 𝒮 Zₐ (fun x => attachedSliceChildCell p L x w hb) s ≫
        DependentFibre.gather R (p.parentVal t) k s ≫ T.map (p.locOuter t ha) (𝟙 k))
      (act 𝒮 Zₐ g ps ≫ DependentFibre.gather R H k ps ≫
        T.map (rectWordChart H (D.slice t.1) (E.slice t.2) ≫
          independentCell R L (D.parentVal t.1) (E.parentVal t.2) (D.slice t.1) (E.slice t.2)
              (D.locOuter t.1 h.1) (E.locOuter t.2 h.2)) (𝟙 k)) := by
  intro p s ps H h h' cs K k g
  let f := D.pairSlice E R L t
  let I := (fun x : p.Slice t => fold 𝒮 Zₐ (fun z => T.obj (p.parentVal t x) (p.childVal t x z))
      (p.terms t w x))
  let J := fun x : D.Slice t.1 × E.Slice t.2 => fold 𝒮 Zₐ (fun z => T.obj (H x) (K x z)) (cs x)
  let a : (I ∘ f) = J := funext fun x =>
    congrArg (fold 𝒮 Zₐ (fun z => T.obj (H x) (K x z))) (D.pairSlice_terms E R L t w x)
  let sd : ps.map f = s := D.pairSlice_word E R L t
  have tr {s' : List (p.Slice t)} (z : s' = s) :
      HEq (act 𝒮 Zₐ (fun x => attachedSliceChildCell p L x w hb) s)
        (act 𝒮 Zₐ (fun x => attachedSliceChildCell p L x w hb) s') := by subst s'; rfl
  have h₁ : HEq (act 𝒮 Zₐ (fun x => attachedSliceChildCell p L x w hb) s) (act 𝒮 Zₐ g ps) :=
    (tr sd).trans ((actRetag_heq (A:=I) (B:=fun x => T.obj (p.parentVal t x) k) f
      (fun x => attachedSliceChildCell p L x w hb) ps).symm.trans
        (act_heq a rfl (D.pairAttachedChild_heq E R L t w hb) ps))
  let P := p.parentVal t
  let b : fold 𝒮 Zₐ P s = fold 𝒮 Zₐ H ps :=
    (congrArg (fold 𝒮 Zₐ P) sd.symm).trans (std_fold_map P f ps)
  have h₂ : HEq (DependentFibre.gather R P k s) (DependentFibre.gather R H k ps) := by
    have gg {s' : List (p.Slice t)} (d : s' = s) :
        HEq (DependentFibre.gather R P k s) (DependentFibre.gather R P k s') := by subst s';rfl
    exact (gg sd).trans (rightGather_map_heq R P rfl f ps).symm
  let o : fold 𝒮 Zₐ H ps ⟶ crossLabel T V' P' t :=
    rectWordChart H (D.slice t.1) (E.slice t.2) ≫
      independentCell R L (D.parentVal t.1) (E.parentVal t.2) (D.slice t.1) (E.slice t.2)
        (D.locOuter t.1 h.1) (E.locOuter t.2 h.2)
  have h₃ : HEq (T.map (p.locOuter t ha) (𝟙 k)) (T.map o (𝟙 k)) :=
    biMap_heq (T:=T) b rfl (rfl : k = k) rfl
      (D.pairLocOuter_heq E R L t ha) (show HEq (𝟙 k) (𝟙 k) from HEq.rfl)
  let pin : fold 𝒮 Zₐ I s = fold 𝒮 Zₐ J ps :=
    ((congrArg (fold 𝒮 Zₐ I) sd.symm).trans (std_fold_map I f ps)).trans
      (congrArg (fun H => fold 𝒮 Zₐ H ps) a)
  let pin' : fold 𝒮 Zₐ (fun x => T.obj (P x) k) s = fold 𝒮 Zₐ (fun x => T.obj (H x) k) ps :=
    (congrArg (fold 𝒮 Zₐ (fun x => T.obj (P x) k)) sd.symm).trans
      (std_fold_map (fun x => T.obj (P x) k) f ps)
  exact structural_seq_heq (K:=coeff (C:=C)) pin pin'
    (rfl : T.obj (crossLabel T V' P' t) k = _)
    h₁
    (structural_seq_heq (K:=coeff (C:=C)) pin' (congrArg (T.obj · k) b)
      (rfl : T.obj (crossLabel T V' P' t) k = _) h₂ h₃)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem OrderedDependentMap.pairSlice_wholeCell
    (t : X' × Y') (w : U' × W') (ha : t ∈ xs'.product ys') (hb : w ∈ crossChildWord us' vs' t)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided]
    [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b) :
    let p := D.independentProduct E R L
    let h := (mem_ordered_product xs' ys' t).mp ha
    let h' := (mem_ordered_product (us' t.1) (vs' t.2) w).mp hb
    HEq (origDependentCell p R L (t,w) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩))
      (jointWordCell (D.slice t.1) (E.slice t.2) (D.terms t.1 w.1) (E.terms t.2 w.2)
        (D.parentVal t.1) (E.parentVal t.2) (D.childVal t.1) (E.childVal t.2) R L
        (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2)
        (D.locOuter t.1 h.1) (E.locOuter t.2 h.2)) := by
  intro p h h'
  let a := D.slice t.1
  let b := E.slice t.2
  let M := D.terms t.1 w.1
  let N := E.terms t.2 w.2
  let k := T.obj (A' t.1 w.1) (B' t.2 w.2)
  let GG := dependentLabels (T:=T) (crossLabel T V P) (crossChildLabel T A B)
  let K := jointLeafLabels (T:=T) (D.parentVal t.1) (E.parentVal t.2) (D.childVal t.1) (E.childVal t.2)
  let F := crossLabel T (D.parentVal t.1) (E.parentVal t.2)
  let o := rectWordChart F a b ≫ independentCell R L (D.parentVal t.1) (E.parentVal t.2) a b
    (D.locOuter t.1 h.1) (E.locOuter t.2 h.2)
  let f := D.pairSlice E R L t
  let s := p.slice t
  let cs := crossChildWord M N
  let ps := a.product b
  let child := crossChildLabel T (D.childVal t.1) (E.childVal t.2)
  let g := fun x => (Lin.left L (F x)).collect (child x) (cs x) ≫
    T.map (𝟙 (F x)) (jointIndexedChildCell R L M N (D.childVal t.1) (E.childVal t.2)
      (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2) x)
  let G := fun (x : p.Slice t) (u : U × W) => (x.val,u)
  let ts := p.terms t w
  let rows₁ := fun x => (ts x).map (G x)
  let rows₂ := fun x => (cs x).map (jointInnerTag x)
  let j := quadOuterRelabel (U:=U) (W:=W)
      (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2 => y.val)
  let h₀ (x : D.Slice t.1 × E.Slice t.2) : rows₁ (f x) =
      (cs x).map (G (f x)) := congrArg (List.map (G (f x))) (D.pairSlice_terms E R L t w x)
  let r₀ : ps.map f = s := D.pairSlice_word E R L t
  let r₁ : ps.flatMap (rows₁ ∘ f) = s.flatMap rows₁ :=
    (List.flatMap_map f rows₁ ps).symm.trans (congrArg (List.flatMap rows₁) r₀)
  let r₂ : (ps.flatMap rows₂).map j = (s.flatMap rows₁).map jointPairRetag := by
    rw [← r₁, List.map_flatMap, List.map_flatMap]
    apply congrArg (fun g => ps.flatMap g)
    funext x
    change (rows₂ x).map j = (rows₁ (f x)).map jointPairRetag
    rw [h₀ x, List.map_map, List.map_map]
    rfl
  let GG' := jointLeafLabels (T:=T) V P A B
  let e₀ : fold 𝒮 Zₐ GG (s.flatMap rows₁) = fold 𝒮 Zₐ K (ps.flatMap rows₂) :=
    ((std_fold_map GG' jointPairRetag (s.flatMap rows₁)).symm.trans
      (congrArg (fold 𝒮 Zₐ GG') r₂.symm)).trans (std_fold_map GG' j (ps.flatMap rows₂))
  let B₀ := fun (x : p.Slice t) => fold 𝒮 Zₐ (GG ∘ G x) (ts x)
  let B₁ := fun x => fold 𝒮 Zₐ (K ∘ jointInnerTag x) (cs x)
  let i₀ : (B₀ ∘ f) = B₁ := funext fun x =>
    congrArg (fold 𝒮 Zₐ (K ∘ jointInnerTag x)) (D.pairSlice_terms E R L t w x)
  let e₁ : fold 𝒮 Zₐ B₀ s = fold 𝒮 Zₐ B₁ ps :=
    ((congrArg (fold 𝒮 Zₐ B₀) r₀.symm).trans (std_fold_map B₀ f ps)).trans
      (congrArg (fun H => fold 𝒮 Zₐ H ps) i₀)
  have z₀ := origDependentCell_flatRows p R L (t,w) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩)
  have z₁ := jointWordCell_flat R L a b M N (D.parentVal t.1) (E.parentVal t.2)
    (D.childVal t.1) (E.childVal t.2) (D.locInner t.1 w.1 h'.1) (E.locInner t.2 w.2 h'.2)
    (D.locOuter t.1 h.1) (E.locOuter t.2 h.2) hl (hr k)
  rw [z₀, z₁]
  apply HEq.trans (hom_source_pin_heq _ _)
  apply HEq.trans _ (hom_source_pin_heq _ _).symm
  exact structural_seq_heq (K:=coeff (C:=C)) e₀ e₁
    (rfl : T.obj (crossLabel T V' P' t) k = _) (D.pairSlice_chart_local E R L t w)
    (D.pairSlice_outputSchedule E R L t w ha hb)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The original joint binary native arrow is literally unary dependent
accumulation of the independently built product of the original inputs,
with an order-preserving retag of its carrier. -/
theorem jointBinaryMap_product_heq
    (hj : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (hd : (dependentWord (xs'.product ys') (crossChildWord us' vs')).Nodup)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided]
    [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b) :
    HEq (origDependentWordMap (D.independentProduct E R L) R L hd) (jointBinaryMap D E R L hj) := by
  let p := D.independentProduct E R L
  let x := dependentWord (xs.product ys) (crossChildWord us vs)
  let y := dependentWord (xs'.product ys') (crossChildWord us' vs')
  let s := (fourJointExpr xs ys us vs).leaves
  let t := (fourJointExpr xs' ys' us' vs').leaves
  let F := jointLeafLabels (T:=T) V P A B
  let G := jointLeafLabels (T:=T) V' P' A' B'
  let e : x.map jointPairRetag = s := jointPairRetag_word xs ys us vs
  let f : y.map jointPairRetag = t := jointPairRetag_word xs' ys' us' vs'
  let k := quadCarrierMap D.parent D.child E.parent E.child
  let ht : t.Nodup := (gridOrder (fourExchangeChart xs' ys' us' vs')).perm.nodup hj
  let a := fun i : Fin y.length => origDependentCell p R L y[i] (List.getElem_mem _)
  let b := fun i : Fin t.length => jointBinaryCell D E R L t[i] (List.getElem_mem _)
  change HEq (wordNativeMap (origDepCarrier p) (origDepCarrier_support p) hd (F ∘ jointPairRetag)
    (G ∘ jointPairRetag) a) (wordNativeMap k (jointSupport D E) ht F G b)
  apply readWordNativeMap_heq F G jointPairRetag jointPairRetag (origDepCarrier p) k
    (origDepCarrier_support p) (jointSupport D E) hd ht e f (fun u _ => independentProduct_carrier D E R L u)
  intro i
  let tt := Fin.cast ((List.length_map (jointPairRetag : ((X' × Y') × (U' × W')) → _)).symm.trans
    (congrArg List.length f)) i
  let u := y[i]
  have hu := (dependentWord_mem (xs'.product ys') (crossChildWord us' vs') u).mp (List.getElem_mem _)
  have h : t[tt] = jointPairRetag u := (retag_word_get jointPairRetag y f i).symm
  have ht' : jointPairRetag u ∈ t := h ▸ List.getElem_mem _
  have hb : HEq (b tt) (jointBinaryCell D E R L (jointPairRetag u) ht') := by
    have j {w z : X' × U' × Y' × W'} (hz : w = z) (hw : w ∈ t) (hz' : z ∈ t) :
        HEq (jointBinaryCell D E R L w hw) (jointBinaryCell D E R L z hz') := by subst z; rfl
    exact j h _ _
  have c := D.pairSlice_wholeCell E R L u.1 u.2 hu.1 hu.2 hl hr
  have d : HEq (jointBinaryCell D E R L (jointPairRetag u) ht') _ :=
    hom_source_pin_heq _ _
  exact c.trans (d.symm.trans hb.symm)

end NativeInput

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
