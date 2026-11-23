module
public import ContextualComposition.NativeJointProductAug
@[expose] public section

/-! Exact product of actual augmented arrows in arbitrary ordered words. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (c : T.obj I I ⟶ I)

def rectangularWordAugCell {X Y : Type u} (A : X → C) (B : Y → C)
    (xs : List X) (ys : List Y) (p : fold 𝒮 Zₐ A xs ⟶ I) (q : fold 𝒮 Zₐ B ys ⟶ I) :
    fold 𝒮 Zₐ (crossLabel T A B) (xs.product ys) ⟶ I :=
  rectWordChart (crossLabel T A B) xs ys ≫ independentCell R L A B xs ys p q ≫ c

set_option backward.isDefEq.respectTransparency false in
theorem totalNativeCell_wordAug {X : Type u}
    (A : X → C) (xs : List X) (p : fold 𝒮 Zₐ A xs ⟶ I) :
    totalNativeCell (wordAug A xs p) = eqToHom (wordTotalPin A xs) ≫ p := by
  unfold totalNativeCell wordAug
  simp only [eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
theorem independentAug_ordered_eq {X Y : Type u} (A : X → C) (B : Y → C)
    (xs : List X) (ys : List Y) (p : fold 𝒮 Zₐ A xs ⟶ I) (q : fold 𝒮 Zₐ B ys ⟶ I) :
    independentAug R L c (wordAug A xs p) (wordAug B ys q) =
      wordAug (crossLabel T A B) (xs.product ys) (rectangularWordAugCell R L c A B xs ys p q) := by
  let S := wordFamily A xs
  let U := wordFamily B ys
  let f := fun i : Fin xs.length => xs[i]
  let g := fun i : Fin ys.length => ys[i]
  let a := totalNativeCell (wordAug A xs p)
  let b := totalNativeCell (wordAug B ys q)
  let e := wordTotalPin A xs
  let d := wordTotalPin B ys
  have hp : HEq a p := (heq_of_eq (totalNativeCell_wordAug A xs p)).trans (hom_source_pin_heq e p)
  have hq : HEq b q := (heq_of_eq (totalNativeCell_wordAug B ys q)).trans (hom_source_pin_heq d q)
  let H := crossLabel T A B
  let xx := independentWord S U
  have rd : xx.map (Prod.map f g) = xs.product ys := readPair_word xs ys
  have hab := rectangleCell_map_heq' R L A B f g (List.finRange xs.length) (List.finRange ys.length)
    (finRange_get xs) (finRange_get ys) hp hq
  let e' := ((std_fold_map H (Prod.map f g) xx).symm.trans (congrArg (fold 𝒮 Zₐ H) rd))
  apply wordAug_read_eq H (Prod.map f g) xx (xs.product ys) rd
  have hr := structural_seq_heq (K:=coeff (C:=C)) e' (rfl : T.obj I I = _) (rfl : I = _)
    hab (show HEq c c from HEq.rfl)
  change HEq ((_ ≫ rowGather R L S.val U.val (List.finRange xs.length) (List.finRange ys.length) ≫
    T.map a b) ≫ c) ((_ ≫ rowGather R L A B xs ys ≫ T.map p q) ≫ c) at hr
  simp only [Category.assoc] at hr
  unfold independentWordAugCell rectangularWordAugCell independentCell
  simp only [Category.assoc]
  exact hr

section Map
variable {X Y X' Y' : Type u} [DecidableEq X'] [DecidableEq Y']
variable {xs : List X} {ys : List Y} {xs' : List X'} {ys' : List Y'}
variable (f : X → X') (g : Y → Y')
variable (hf : ∀ x ∈ xs, f x ∈ xs') (hg : ∀ y ∈ ys, g y ∈ ys')
variable (A : X → C) (B : Y → C) (A' : X' → C) (B' : Y' → C)
variable (hn : xs'.Nodup) (hm : ys'.Nodup)
variable (p : ∀ t ∈ xs', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A (wordFibre xs f t) ⟶ A' t)
variable (q : ∀ t ∈ ys', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B (wordFibre ys g t) ⟶ B' t)

include hf hg in
omit [DecidableEq X'] [DecidableEq Y'] in
theorem rectangularWordSupport : ∀ x ∈ xs.product ys, Prod.map f g x ∈ xs'.product ys' := by
  intro x hx
  have m := (mem_ordered_product xs ys x).mp hx
  exact (mem_ordered_product xs' ys' _).mpr ⟨hf _ m.1,hg _ m.2⟩

noncomputable def rectangularWordMap :
    Hom ℙ (wordFamily (crossLabel T A B) (xs.product ys))
      (wordFamily (crossLabel T A' B') (xs'.product ys')) :=
  wordNativeMap (Prod.map f g) (rectangularWordSupport f g hf hg) (nodup_product_word hn hm)
    (crossLabel T A B) (crossLabel T A' B')
    (fun j => let m := (mem_ordered_product xs' ys' _).mp (show (xs'.product ys')[j] ∈ xs'.product ys' from List.getElem_mem _)
      rectangularWordCell R L xs ys f g (xs'.product ys')[j] A B (p _ m.1) (q _ m.2))

set_option backward.isDefEq.respectTransparency false in
theorem rectangularWordCell_read_heq
    (t : Fin xs'.length × Fin ys'.length) :
    let P := wordNativeMap f hf hn A A' (fun j => p xs'[j] (List.getElem_mem _))
    let Q := wordNativeMap g hg hm B B' (fun j => q ys'[j] (List.getElem_mem _))
    HEq (independentWordCell T P Q R L t)
      (rectangularWordCell R L xs ys f g (readPair xs' ys' t) A B
        (p xs'[t.1] (List.getElem_mem _)) (q ys'[t.2] (List.getElem_mem _))) := by
  intro P Q
  let F := fun i : Fin xs.length => xs[i]
  let G := fun i : Fin ys.length => ys[i]
  have e : (fibreList P.addr t.1).map F = wordFibre xs f xs'[t.1] :=
    wordCarrier_fibre f hf hn t.1
  have e' : (fibreList Q.addr t.2).map G = wordFibre ys g ys'[t.2] :=
    wordCarrier_fibre g hg hm t.2
  have a : HEq (P.cell t.1) (p xs'[t.1] (List.getElem_mem _)) := hom_source_pin_heq _ _
  have b : HEq (Q.cell t.2) (q ys'[t.2] (List.getElem_mem _)) := hom_source_pin_heq _ _
  have h := rectangleCell_map_heq' R L A B F G (fibreList P.addr t.1) (fibreList Q.addr t.2) e e' a b
  exact (hom_source_pin_heq _ _).trans (h.trans (hom_source_pin_heq _ _).symm)

set_option backward.isDefEq.respectTransparency false in
theorem rectangularWordMap_read_heq :
    let P := wordNativeMap f hf hn A A' (fun j => p xs'[j] (List.getElem_mem _))
    let Q := wordNativeMap g hg hm B B' (fun j => q ys'[j] (List.getElem_mem _))
    HEq (independentNativeWordMap T P Q R L) (rectangularWordMap R L f g hf hg A B A' B' hn hm p q) := by
  intro P Q
  let s := independentWord (wordFamily A xs) (wordFamily B ys)
  let t := independentWord (wordFamily A' xs') (wordFamily B' ys')
  let u := xs'.product ys'
  let F := readPair xs ys
  let G := readPair xs' ys'
  let h : s.map F = xs.product ys := readPair_word xs ys
  let j : t.map G = u := readPair_word xs' ys'
  let R' := rectangularWordSupport f g hf hg
  let K := crossLabel T A B
  let H := crossLabel T A' B'
  let cc (x : X' × Y') (hx : x ∈ u) :=
    let h := (mem_ordered_product xs' ys' x).mp hx
    rectangularWordCell R L xs ys f g x A B (p _ h.1) (q _ h.2)
  change HEq (wordNativeMap (Prod.map P.addr Q.addr) (independent_word_support P Q)
    (independentWord_nodup _ _) (K ∘ F) (H ∘ G) (fun i => independentWordCell T P Q R L t[i]))
    (wordNativeMap (Prod.map f g) R' (nodup_product_word hn hm) K H
      (fun i => cc u[i] (List.getElem_mem _)))
  apply readWordNativeMap_heq K H F G (Prod.map P.addr Q.addr) (Prod.map f g)
    (independent_word_support P Q) R' (independentWord_nodup _ _) (nodup_product_word hn hm) h j
  · intro a _
    exact Prod.ext (wordCarrier_get f hf hn a.1) (wordCarrier_get g hg hm a.2)
  · intro i
    let z := t[i]
    let k := Fin.cast ((List.length_map G).symm.trans (congrArg List.length j)) i
    have a : G z = u[k] := retag_word_get G t j i
    let hs : G z ∈ u := a.symm ▸ List.getElem_mem _
    have b : HEq (cc (G z) hs) (cc u[k] (List.getElem_mem _)) := by
      have he {x y : X' × Y'} (z : x = y) (h : x ∈ u) (h' : y ∈ u) :
          HEq (cc x h) (cc y h') := by subst y; rfl
      exact he a hs (List.getElem_mem _)
    exact (rectangularWordCell_read_heq R L f g hf hg A B A' B' hn hm p q z).trans b

set_option backward.isDefEq.respectTransparency false in
theorem nativeAug_preserving_heq {S D S' D' : Aug ℙ I}
    (p : AugHom ℙ S D) (q : Hom ℙ S'.base D'.base)
    (e : S = S') (f : D = D') (g : HEq p.native q) :
    q.comp D'.ε = S'.ε := by
  subst S'
  subst D'
  rw [← eq_of_heq g]
  exact p.preserves

set_option backward.isDefEq.respectTransparency false in
theorem rectangularWordMap_preserves
    (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (a' : fold 𝒮 Zₐ A' xs' ⟶ I) (b' : fold 𝒮 Zₐ B' ys' ⟶ I)
    (h₁ : (wordNativeMap f hf hn A A' (fun j => p xs'[j] (List.getElem_mem _))).comp
      (wordAug A' xs' a').ε = (wordAug A xs a).ε)
    (h₂ : (wordNativeMap g hg hm B B' (fun j => q ys'[j] (List.getElem_mem _))).comp
      (wordAug B' ys' b').ε = (wordAug B ys b).ε) :
    (rectangularWordMap R L f g hf hg A B A' B' hn hm p q).comp
      (wordAug (crossLabel T A' B') (xs'.product ys')
        (rectangularWordAugCell R L c A' B' xs' ys' a' b')).ε =
      (wordAug (crossLabel T A B) (xs.product ys) (rectangularWordAugCell R L c A B xs ys a b)).ε := by
  let P : AugHom ℙ (wordAug A xs a) (wordAug A' xs' a') := ⟨_,h₁⟩
  let Q : AugHom ℙ (wordAug B ys b) (wordAug B' ys' b') := ⟨_,h₂⟩
  let M := independentAugMap R L c N NR NL hl hr P Q
  have ee := independentAug_ordered_eq R L c A B xs ys a b
  have ff := independentAug_ordered_eq R L c A' B' xs' ys' a' b'
  exact nativeAug_preserving_heq M _ ee ff (rectangularWordMap_read_heq R L f g hf hg A B A' B' hn hm p q)

end Map
section ProductDependent
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

include N NR NL hl hr in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
/-- Both actual product input arrows preserve their own product
augmentations, before any dependent accumulation is applied. -/
theorem OrderedDependentMap.independentProduct_preserves
    {hn : xs'.Nodup} {hm : ys'.Nodup}
    {hD : ∀ x ∈ xs, (us' (D.parent x)).Nodup}
    {hE : ∀ y ∈ ys, (vs' (E.parent y)).Nodup}
    {δ : ∀ x, fold 𝒮 Zₐ (A x) (us x) ⟶ I} {η : ∀ y, fold 𝒮 Zₐ (B y) (vs y) ⟶ I}
    {δ' : ∀ x, fold 𝒮 Zₐ (A' x) (us' x) ⟶ I} {η' : ∀ y, fold 𝒮 Zₐ (B' y) (vs' y) ⟶ I}
    {ε : fold 𝒮 Zₐ V xs ⟶ I} {γ : fold 𝒮 Zₐ P ys ⟶ I}
    {ε' : fold 𝒮 Zₐ V' xs' ⟶ I} {γ' : fold 𝒮 Zₐ P' ys' ⟶ I}
    (h₁ : D.Preserves hn hD δ δ' ε ε') (h₂ : E.Preserves hm hE η η' γ γ') :
    (D.independentProduct E R L).Preserves (nodup_product_word hn hm)
      (fun t ht => let h := (mem_ordered_product xs ys t).mp ht
        nodup_product_word (hD t.1 h.1) (hE t.2 h.2))
      (fun t => rectangularWordAugCell R L c (A t.1) (B t.2) (us t.1) (vs t.2) (δ t.1) (η t.2))
      (fun t => rectangularWordAugCell R L c (A' t.1) (B' t.2) (us' t.1) (vs' t.2) (δ' t.1) (η' t.2))
      (rectangularWordAugCell R L c V P xs ys ε γ) (rectangularWordAugCell R L c V' P' xs' ys' ε' γ') := by
  constructor
  · exact rectangularWordMap_preserves R L c D.parent E.parent D.parent_mem E.parent_mem
      V P V' P' hn hm D.outer E.outer N NR NL hl hr ε γ ε' γ' h₁.outer h₂.outer
  · intro t ht
    have h := (mem_ordered_product xs ys t).mp ht
    exact rectangularWordMap_preserves R L c (D.child t.1) (E.child t.2)
      (D.child_mem t.1 h.1) (E.child_mem t.2 h.2)
      (A t.1) (B t.2) (A' (D.parent t.1)) (B' (E.parent t.2))
      (hD _ h.1) (hE _ h.2) (D.inner _ h.1) (E.inner _ h.2) N NR NL hl hr
      (δ t.1) (η t.2) (δ' (D.parent t.1)) (η' (E.parent t.2)) (h₁.inner _ h.1) (h₂.inner _ h.2)

end ProductDependent

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
