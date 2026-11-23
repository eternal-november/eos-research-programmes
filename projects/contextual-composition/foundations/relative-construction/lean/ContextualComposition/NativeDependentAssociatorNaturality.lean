module
public import ContextualComposition.NativeDependentTripleFibre
public import ContextualComposition.NativeWordRetagMap
@[expose] public section

/-! Natural dependent associator on the literal nested augmented maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

theorem NativeAugmentedIso.retarget_native_heq {I : C} {A B D E : Aug ℙ I}
    (p : NativeAugmentedIso A B) (h : A = D) (k : B = E) :
    HEq (p.retarget h k).hom.native p.hom.native := by
  subst D
  subst E
  rfl

section Frame

variable {T : Bi (coeff (C:=C))}
variable (P : TensorPrimitive T)
variable {X Y W : Type u}
variable (V : X → C) (B : X → Y → C) (D : X → Y → W → C)

noncomputable def associatorTripleIso (ι : ∀ a b c, IsIso (P.assoc a b c)) (t : X × Y × W) :
    (assocLeftLabels T V B D ∘ tripleRetag.symm) t ≅ assocRightLabels T V B D t := by
  exact @asIso C _ _ _ (P.assoc (V t.1) (B t.1 t.2.1) (D t.1 t.2.1 t.2.2))
    (ι (V t.1) (B t.1 t.2.1) (D t.1 t.2.1 t.2.2))

noncomputable def dependentAssocFrame (ι : ∀ a b c, IsIso (P.assoc a b c))
    {w : List (X × Y × W)} (h : w.Nodup) :
    Hom ℙ (wordFamily (assocLeftLabels T V B D ∘ tripleRetag.symm) w)
      (wordFamily (assocRightLabels T V B D) w) :=
  nativeReindex (wordEquiv (AddressOrder.ident w).perm h)
    (wordComparisonCells _ _ (.ident w) h (associatorTripleIso P V B D ι))

set_option backward.isDefEq.respectTransparency false in
theorem dependentAssocIso_frame_heq
    {I : C} (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (J : UnitCompat R I) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
    (xs : List X) (ys : X → List Y) (ws : X → Y → List W)
    (ε : fold 𝒮 Zₐ V xs ⟶ I) (δ : ∀ x, fold 𝒮 Zₐ (B x) (ys x) ⟶ I)
    (γ : ∀ x y, fold 𝒮 Zₐ (D x y) (ws x y) ⟶ I)
    (ι : ∀ a b c, IsIso (P.assoc a b c))
    (hn : (dependentWord xs (fun x => dependentWord (ys x) (ws x))).Nodup) :
    HEq (dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι hn).hom.native
      (dependentAssocFrame P V B D ι hn) := by
  unfold dependentAssocIso dependentAssocFrame associatorTripleIso
  dsimp only
  apply NativeAugmentedIso.retarget_native_heq

end Frame

section Native
variable {T : Bi (coeff (C:=C))}
variable {X Y W X' Y' W' : Type u} [DecidableEq X'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : X → List Y} {ws : X → Y → List W}
variable {xs' : List X'} {ys' : X' → List Y'} {ws' : X' → Y' → List W'}
variable {V : X → C} {B : X → Y → C} {D : X → Y → W → C}
variable {V' : X' → C} {B' : X' → Y' → C} {D' : X' → Y' → W' → C}
variable (F : OrderedDependentMap xs ys xs' ys' V B V' B')
variable (G : OrderedThirdMap F ws ws' D D')
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (P : TensorPrimitive T)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided]
variable [rF : ∀ a : C, (rightFactor (T:=T) a).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L)
variable (hr : ∀ a : C, SameRightGather R a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
include NR NL Q hl hr in
theorem dependentAssoc_retagCell_square (t : X' × Y' × W')
    (ht : t ∈ dependentWord xs' (fun x => dependentWord (ys' x) (ws' x))) :
    let U := G.leftInput F R L
    let V₀ := G.rightInput F R L
    let Rs := dependentWord xs (fun x => dependentWord (ys x) (ws x))
    let T₀ := assocLeftLabels T V B D ∘ tripleRetag.symm
    let T₁ := assocLeftLabels T V' B' D' ∘ tripleRetag.symm
    let p := fun t ht => origDependentCell U R L t ht
    let p' := retagWordCell tripleRetag tripleRetag (origDepCarrier U) (origDepCarrier V₀)
      (G.associator_carrier F R L) (tripleRetag_word xs ys ws) (tripleRetag_word xs' ys' ws') T₀ T₁ p
    p' t ht ≫ P.assoc (V' t.1) (B' t.1 t.2.1) (D' t.1 t.2.1 t.2.2) =
      act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2))
        (wordFibre Rs (origDepCarrier V₀) t) ≫ origDependentCell V₀ R L t ht := by
  intro U V₀ Rs T₀ T₁ p p'
  let Ls := dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2)
  rcases t with ⟨a,b,d⟩
  let h := (dependentWord_mem xs' (fun x => dependentWord (ys' x) (ws' x)) (a,b,d)).mp ht
  let k := (dependentWord_mem (ys' a) (ws' a) (b,d)).mp h.2
  let ha := h.1
  let hb := k.1
  let hd := k.2
  let ht' : ((a,b),d) ∈ dependentWord (dependentWord xs' ys') (fun p => ws' p.1 p.2) :=
    (dependentWord_mem _ _ _).mpr ⟨(dependentWord_mem _ _ _).mpr ⟨ha,hb⟩,hd⟩
  let LK := G.leftFinalSchedule F R L a b d ha hb hd
  let RK := G.rightFinalSchedule F R L a b d ha hb hd
  let f := origDepCarrier U
  let g := origDepCarrier V₀
  let l := (F.slice a).flatMap (G.leftFinalWords F a b d)
  let r := (F.slice a).flatMap (G.rightFinalWords F a b d)
  let l₀ := wordFibre Ls f ((a,b),d)
  let r₀ := wordFibre Rs g (a,b,d)
  let A₀ := assocLeftLabels T V B D
  let A₁ := assocRightLabels T V B D
  let z := P.assoc (V' a) (B' a b) (D' a b d)
  let φ := fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2)
  have hh₁ := G.leftFinalWords_fibre F R L a b d
  have hh₂ := G.rightFinalWords_fibre F R L a b d
  let M : l₀.map tripleRetag = r₀ :=
    (retag_wordFibre tripleRetag tripleRetag f g (G.associator_carrier F R L) ((a,b),d)).trans
      (congrArg (fun w => wordFibre w g (a,b,d)) (tripleRetag_word xs ys ws))
  let e₀ : fold 𝒮 Zₐ T₀ r₀ = fold 𝒮 Zₐ A₀ l :=
    ((congrArg (fold 𝒮 Zₐ T₀) M.symm).trans (std_fold_map T₀ tripleRetag l₀)).trans
      (congrArg (fold 𝒮 Zₐ A₀) hh₁.symm)
  have l₁ : HEq (p' (a,b,d) ht) LK :=
    (retagWordCell_heq tripleRetag tripleRetag f g (G.associator_carrier F R L)
      (tripleRetag_word xs ys ws) (tripleRetag_word xs' ys' ws') T₀ T₁ p ((a,b),d) ht' ht).trans
        (G.leftFinalSchedule_heq F R L a b d ha hb hd NR (hr _))
  have hl₁ : HEq (p' (a,b,d) ht ≫ z) (LK ≫ z) :=
    structural_seq_heq (K:=coeff (C:=C)) e₀ (rfl : T.obj (T.obj (V' a) (B' a b)) (D' a b d) = _)
      (rfl : T.obj (V' a) (T.obj (B' a b) (D' a b d)) = _) l₁ (show HEq z z from HEq.rfl)
  have hR : HEq (act 𝒮 Zₐ φ r ≫ RK) (act 𝒮 Zₐ φ r₀ ≫ origDependentCell V₀ R L (a,b,d) ht) := by
    have H {s t : List (X × Y × W)} (e : s = t) : HEq (act 𝒮 Zₐ φ s) (act 𝒮 Zₐ φ t) := by cases e; rfl
    exact structural_seq_heq (K:=coeff (C:=C)) (congrArg (fold 𝒮 Zₐ T₀) hh₂)
      (congrArg (fold 𝒮 Zₐ A₁) hh₂) (rfl : T.obj (V' a) (T.obj (B' a b) (D' a b d)) = _)
      (H hh₂) (G.rightFinalSchedule_heq F R L a b d ha hb hd).symm
  exact eq_of_heq (hl₁.trans ((G.finalSchedules_square F R L a b d ha hb hd P NR NL Q hl).trans hR))

section Square
variable {I : C} (J : UnitCompat R I) (U : AssocRightUnit R J P)
variable (ι : ∀ a b c, IsIso (P.assoc a b c))
variable (ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I)
variable (ε' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V' xs' ⟶ I)
variable (δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I)
variable (δ' : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B' x) (ys' x) ⟶ I)
variable (γ : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ I)
variable (γ' : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D' x y) (ws' x y) ⟶ I)
variable (hxR : (dependentWord xs (fun x => dependentWord (ys x) (ws x))).Nodup)
variable (hyR : (dependentWord xs' (fun x => dependentWord (ys' x) (ws' x))).Nodup)
variable (hyL : (dependentWord (dependentWord xs' ys') (fun x => ws' x.1 x.2)).Nodup)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3800000 in
include NR hr in
/-- Naturality under arbitrary carrier-changing maps, using both original
native routes and the literal associator. -/
theorem actual_dependent_assoc_native_square :
    (origDependentWordMap (G.leftInput F R L) R L hyL).comp
      (dependentAssocIso R L J P NL Q U xs' ys' ws' V' B' D' ε' δ' γ' hl ι hyR).hom.native =
    (dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι hxR).hom.native.comp
      (origDependentWordMap (G.rightInput F R L) R L hyR) := by
  let l := G.leftInput F R L
  let r := G.rightInput F R L
  let xsL := dependentWord (dependentWord xs ys) (fun x => ws x.1 x.2)
  let ysL := dependentWord (dependentWord xs' ys') (fun x => ws' x.1 x.2)
  let xsR := dependentWord xs (fun x => dependentWord (ys x) (ws x))
  let ysR := dependentWord xs' (fun x => dependentWord (ys' x) (ws' x))
  let r₀ := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let r₁ := tripleRetag (X:=X') (Y:=Y') (W:=W')
  let rs : xsL.map r₀ = xsR := tripleRetag_word xs ys ws
  let rt : ysL.map r₁ = ysR := tripleRetag_word xs' ys' ws'
  let A := assocLeftLabels T V B D ∘ r₀.symm
  let B₀ := assocLeftLabels T V' B' D' ∘ r₁.symm
  let A' := assocRightLabels T V B D
  let B₀' := assocRightLabels T V' B' D'
  let f := origDepCarrier l
  let g := origDepCarrier r
  let p := fun t ht => origDependentCell l R L t ht
  let q := fun t ht => origDependentCell r R L t ht
  let p' := retagWordCell r₀ r₁ f g (G.associator_carrier F R L) rs rt A B₀ p
  let hs := origDepCarrier_support r
  let α := associatorTripleIso P V B D ι
  let β := associatorTripleIso P V' B' D' ι
  let e := dependentAssocFrame P V B D ι hxR
  let e' := dependentAssocFrame P V' B' D' ι hyR
  let u := origDependentWordMap l R L hyL
  let v := origDependentWordMap r R L hyR
  let w := wordNativeMap g hs hyR A B₀ (fun i => p' ysR[i] (List.getElem_mem _))
  let x := (dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι hxR).hom.native
  let y := (dependentAssocIso R L J P NL Q U xs' ys' ws' V' B' D' ε' δ' γ' hl ι hyR).hom.native
  have h : ∀ t (ht : t ∈ ysR), p' t ht ≫ (β t).hom =
      act 𝒮 Zₐ (fun t => (α t).hom) (wordFibre xsR g t) ≫ q t ht :=
    dependentAssoc_retagCell_square F G R L P NR NL Q hl hr
  have hh : w.comp e' = e.comp v :=
    wordNativeMap_identChart_square g hs hxR hyR A A' B₀ B₀' α β p' q h
  have hu : HEq u w := retagWordMap_heq r₀ r₁ f g (G.associator_carrier F R L) rs rt A B₀ p
    (origDepCarrier_support l) hyL hyR
  have hx : HEq x e := dependentAssocIso_frame_heq P V B D R L J NL Q U hl xs ys ws ε δ γ ι hxR
  have hy : HEq y e' := dependentAssocIso_frame_heq P V' B' D' R L J NL Q U hl xs' ys' ws' ε' δ' γ' ι hyR
  have xx := wordFamily_read_eq A r₀ xsL xsR rs
  have yy := wordFamily_read_eq B₀ r₁ ysL ysR rt
  exact eq_of_heq ((nativeHom_comp_heq u y w e' xx yy rfl hu hy).trans
    ((heq_of_eq hh).trans (nativeHom_comp_heq x v e v xx rfl rfl hx HEq.rfl).symm))

section Augmented
variable [DecidableEq X] [DecidableEq Y]
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (hx : xs.Nodup) (hx' : xs'.Nodup)
variable (hy : ∀ x ∈ xs, (ys x).Nodup) (hy' : ∀ x ∈ xs', (ys' x).Nodup)
variable (hw : ∀ x ∈ xs, ∀ y ∈ ys x, (ws x y).Nodup)
variable (hw' : ∀ x ∈ xs', ∀ y ∈ ys' x, (ws' x y).Nodup)
variable (p : F.Preserves hx' (fun x hx => hy' _ (F.parent_mem x hx)) δ δ' ε ε')
variable (q : G.Preserves F (fun x hx y hy => hw' _ (F.parent_mem x hx) _ (F.child_mem x hx y hy)) γ γ')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
include NR hr in
/-- Naturality of the actual augmented dependent associator on both
independently constructed three-layer carrier-changing augmented maps. -/
theorem actual_dependent_assoc_augmented_square :
    let sx := dependentWord_nodup hx (fun x h => dependentWord_nodup (hy x h) (hw x h))
    let tx := dependentWord_nodup hx' (fun x h => dependentWord_nodup (hy' x h) (hw' x h))
    (G.leftAugMap F R L J N NL hl hx hx' hy hy' hw hw' p q).comp
      (dependentAssocIso R L J P NL Q U xs' ys' ws' V' B' D' ε' δ' γ' hl ι tx).hom =
    (dependentAssocIso R L J P NL Q U xs ys ws V B D ε δ γ hl ι sx).hom.comp
      (G.rightAugMap F R L J N NL hl hx hx' hy hy' hw hw' p q) := by
  intro sx tx
  apply AugHom.ext
  exact actual_dependent_assoc_native_square F G R L P NR NL Q hl hr J U ι ε ε' δ δ' γ γ' sx tx
    (dependentWord_nodup (dependentWord_nodup hx' hy')
      (fun t ht => let h := (dependentWord_mem xs' ys' t).mp ht; hw' _ h.1 _ h.2))

end Augmented

end Square
end Native

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
