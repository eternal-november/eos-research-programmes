module
public import ContextualComposition.NativeIndependentWordArrow
@[expose] public section

/-! Naturality of the actual independent associator over arbitrary
carrier-changing input maps, comparing each original selected whole cell. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem independentFamily_word {X Y : Type u} (A : X → C) (B : Y → C)
    (xs : List X) (ys : List Y) :
    independentFamily T (wordFamily A xs) (wordFamily B ys) = wordFamily (crossLabel T A B) (xs.product ys) :=
  wordFamily_read_eq (crossLabel T A B) (readPair xs ys) _ _ (readPair_word xs ys)

theorem independentNativeWordMap_heq {A B D E A' B' D' E' : Family C}
    (ha : A = A') (hb : B = B') (hd : D = D') (he : E = E')
    (p : Hom ℙ A B) (q : Hom ℙ D E) (p' : Hom ℙ A' B') (q' : Hom ℙ D' E')
    (hp : HEq p p') (hq : HEq q q') :
    HEq (independentNativeWordMap T p q R L) (independentNativeWordMap T p' q' R L) := by
  subst A'; subst B'; subst D'; subst E'
  cases hp
  cases hq
  rfl

section Triple
variable {X Y W X' Y' W' : Type u} [DecidableEq X'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {ws : List W} {xs' : List X'} {ys' : List Y'} {ws' : List W'}
variable (A : X → C) (B : Y → C) (D : W → C) (A' : X' → C) (B' : Y' → C) (D' : W' → C)
variable (f : X → X') (g : Y → Y') (k : W → W')
variable (hf : ∀ a ∈ xs, f a ∈ xs') (hg : ∀ a ∈ ys, g a ∈ ys') (hk : ∀ a ∈ ws, k a ∈ ws')
variable (hx' : xs'.Nodup) (hy' : ys'.Nodup) (hw' : ws'.Nodup)
variable (p : ∀ x ∈ xs', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A (wordFibre xs f x) ⟶ A' x)
variable (q : ∀ y ∈ ys', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B (wordFibre ys g y) ⟶ B' y)
variable (r : ∀ w ∈ ws', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D (wordFibre ws k w) ⟶ D' w)
set_option quotPrecheck false in
local notation "pNative" => wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _))
set_option quotPrecheck false in
local notation "qNative" => wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))
set_option quotPrecheck false in
local notation "rNative" => wordNativeMap k hk hw' D D' (fun j => r ws'[j] (List.getElem_mem _))
local notation "pqCell" => wordProductCell R L f g A B A' B' p q
local notation "qrCell" => wordProductCell R L g k B D B' D' q r
local notation "ab" => crossLabel T A B
local notation "ab'" => crossLabel T A' B'
local notation "bd" => crossLabel T B D
local notation "bd'" => crossLabel T B' D'
local notation "al" => crossLabel T (crossLabel T A B) D
local notation "al'" => crossLabel T (crossLabel T A' B') D'
local notation "ar" => crossLabel T A (crossLabel T B D)
local notation "ar'" => crossLabel T A' (crossLabel T B' D')
set_option quotPrecheck false in
local notation "wl" => (xs.product ys).product ws
set_option quotPrecheck false in
local notation "wl'" => (xs'.product ys').product ws'
set_option quotPrecheck false in
local notation "wr" => xs.product (ys.product ws)
set_option quotPrecheck false in
local notation "wr'" => xs'.product (ys'.product ws')
local notation "fl" => Prod.map (Prod.map f g) k
local notation "fr" => Prod.map f (Prod.map g k)
local notation "lCell" => wordProductCell R L (Prod.map f g) k ab D ab' D' pqCell r
local notation "rCell" => wordProductCell R L f (Prod.map g k) A bd A' bd' p qrCell

set_option backward.isDefEq.respectTransparency false in
theorem independentTripleLeftMap_heq :
    HEq (independentNativeWordMap T (independentNativeWordMap T pNative qNative R L) rNative R L)
      (wordProductMap R L (Prod.map f g) k ab D ab' D' pqCell r
        (wordProduct_support f g hf hg) hk (nodup_product_word hx' hy') hw') := by
  let m := wordProductMap R L f g A B A' B' p q hf hg hx' hy'
  have h := wordProductMap_original_heq R L f g A B A' B' p q hf hg hx' hy'
  have e := independentFamily_word (T:=T) A B xs ys
  have e' := independentFamily_word (T:=T) A' B' xs' ys'
  exact ((independentNativeWordMap_heq R L e e' rfl rfl _ rNative m rNative h HEq.rfl).trans
    (wordProductMap_original_heq R L (Prod.map f g) k ab D ab' D' pqCell r
      (wordProduct_support f g hf hg) hk (nodup_product_word hx' hy') hw'))

set_option backward.isDefEq.respectTransparency false in
theorem independentTripleRightMap_heq :
    HEq (independentNativeWordMap T pNative (independentNativeWordMap T qNative rNative R L) R L)
      (wordProductMap R L f (Prod.map g k) A bd A' bd' p qrCell
        hf (wordProduct_support g k hg hk) hx' (nodup_product_word hy' hw')) := by
  let m := wordProductMap R L g k B D B' D' q r hg hk hy' hw'
  have h := wordProductMap_original_heq R L g k B D B' D' q r hg hk hy' hw'
  have e := independentFamily_word (T:=T) B D ys ws
  have e' := independentFamily_word (T:=T) B' D' ys' ws'
  exact ((independentNativeWordMap_heq R L rfl rfl e e' pNative _ pNative m HEq.rfl h).trans
    (wordProductMap_original_heq R L f (Prod.map g k) A bd A' bd' p qrCell
      hf (wordProduct_support g k hg hk) hx' (nodup_product_word hy' hw')))


set_option backward.isDefEq.respectTransparency false in
theorem independentTripleLeftCell_heq (t : (X' × Y') × W') (ht : t ∈ wl') :
    let x := t.1.1
    let y := t.1.2
    let w := t.2
    let h₀ := (dependentWord_mem _ (fun _ => ws') t).mp ht
    let h₁ := (dependentWord_mem xs' (fun _ => ys') t.1).mp h₀.1
    HEq (lCell t ht) (tripleIndependentLeftCell R L A B D
      (wordFibre xs f x) (wordFibre ys g y) (wordFibre ws k w) (p x h₁.1) (q y h₁.2) (r w h₀.2)) := by
  intro x y w h₀ h₁
  let u := wordFibre xs f x
  let v := wordFibre ys g y
  let s := wordFibre ws k w
  let l := wordFibre (xs.product ys) (Prod.map f g) t.1
  let τ := rectWordChart ab u v ≫ independentCell R L A B u v (p x h₁.1) (q y h₁.2)
  have h : l.map id = u.product v := (List.map_id l).trans (product_word_fibre xs ys f g t.1)
  have ep : HEq (pqCell t.1 h₀.1) τ := hom_source_pin_heq _ _
  have a := rectangleCell_map_heq' R L ab D id id l s h (List.map_id s) ep
    (HEq.rfl : HEq (r w h₀.2) (r w h₀.2))
  exact (hom_source_pin_heq _ _).trans a

set_option backward.isDefEq.respectTransparency false in
theorem independentTripleRightCell_heq (t : X' × Y' × W') (ht : t ∈ wr') :
    let x := t.1
    let y := t.2.1
    let w := t.2.2
    let h₀ := (dependentWord_mem xs' (fun _ => ys'.product ws') t).mp ht
    let h₁ := (dependentWord_mem ys' (fun _ => ws') t.2).mp h₀.2
    HEq (rCell t ht) (tripleIndependentRightCell R L A B D
      (wordFibre xs f x) (wordFibre ys g y) (wordFibre ws k w) (p x h₀.1) (q y h₁.1) (r w h₁.2)) := by
  intro x y w h₀ h₁
  let u := wordFibre xs f x
  let v := wordFibre ys g y
  let s := wordFibre ws k w
  let l := wordFibre (ys.product ws) (Prod.map g k) t.2
  let τ := rectWordChart bd v s ≫ independentCell R L B D v s (q y h₁.1) (r w h₁.2)
  have h : l.map id = v.product s := (List.map_id l).trans (product_word_fibre ys ws g k t.2)
  have ep : HEq (qrCell t.2 h₀.2) τ := hom_source_pin_heq _ _
  have a := rectangleCell_map_heq' R L A bd id id u l (List.map_id u) h
    (HEq.rfl : HEq (p x h₀.1) (p x h₀.1)) ep
  exact (hom_source_pin_heq _ _).trans a


variable (P : TensorPrimitive T) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (Q : PrimitiveLinearity R L P)
variable [lF : ∀ c : C, (leftFactor T c).LaxBraided] [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided]
variable (hl : ∀ c : C, SameLeftGather T c L) (hr : ∀ c : C, SameRightGather R c)
set_option quotPrecheck false in
local notation "readIn" => (tripleRetag (X:=X) (Y:=Y) (W:=W))
set_option quotPrecheck false in
local notation "readOut" => (tripleRetag (X:=X') (Y:=Y') (W:=W'))
set_option quotPrecheck false in
local notation "readIn_word" => tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)
set_option quotPrecheck false in
local notation "readOut_word" => tripleRetag_word xs' (fun _ => ys') (fun _ _ => ws')
set_option quotPrecheck false in
local notation "leftRead" => (al ∘ (readIn).symm)
set_option quotPrecheck false in
local notation "leftRead'" => (al' ∘ (readOut).symm)
set_option quotPrecheck false in
local notation "readCell" => retagWordCell readIn readOut fl fr (fun _ => rfl) readIn_word readOut_word leftRead leftRead' lCell

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
include NR NL Q hl hr in
theorem independentTripleCell_square (t : X' × Y' × W') (ht : t ∈ wr') :
    readCell t ht ≫ P.assoc (A' t.1) (B' t.2.1) (D' t.2.2) =
      act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)) (wordFibre wr fr t) ≫
        rCell t ht := by
  rcases t with ⟨x,y,w⟩
  let t₀ : (X' × Y') × W' := ((x,y),w)
  let t : X' × Y' × W' := (x,y,w)
  let h₀ := (dependentWord_mem xs' (fun _ => ys'.product ws') t).mp ht
  let h₁ := (dependentWord_mem ys' (fun _ => ws') t.2).mp h₀.2
  let hm : t₀ ∈ wl' := (dependentWord_mem _ (fun _ => ws') t₀).mpr
    ⟨(dependentWord_mem xs' (fun _ => ys') (x,y)).mpr ⟨h₀.1,h₁.1⟩, h₁.2⟩
  let u := wordFibre xs f x
  let v := wordFibre ys g y
  let s := wordFibre ws k w
  let F := wordFibre wr fr t
  let D₀ := fold 𝒮 Zₐ leftRead
  let D₁ := fold 𝒮 Zₐ ar
  let P₀ := tripleIndependentLeftCell R L A B D u v s (p x h₀.1) (q y h₁.1) (r w h₁.2)
  let P₁ := tripleIndependentRightCell R L A B D u v s (p x h₀.1) (q y h₁.1) (r w h₁.2)
  let α (z : X × Y × W) : leftRead z ⟶ ar z := P.assoc (A z.1) (B z.2.1) (D z.2.2)
  let β := P.assoc (A' x) (B' y) (D' w)
  have hs : F = u.product (v.product s) := (product_word_fibre xs (ys.product ws) f (Prod.map g k) t).trans
    (congrArg (List.product u) (product_word_fibre ys ws g k (y,w)))
  have eh := retagWordCell_heq readIn readOut fl fr (fun _ => rfl) readIn_word readOut_word leftRead leftRead'
    lCell t₀ hm ht
  have hL : HEq (readCell t ht) P₀ :=
    eh.trans (independentTripleLeftCell_heq R L A B D A' B' D' f g k p q r t₀ hm)
  have hR : HEq (rCell t ht) P₁ := independentTripleRightCell_heq R L A B D A' B' D' f g k p q r t ht
  have hEq : D₀ F = fold 𝒮 Zₐ al ((u.product v).product s) :=
    (congrArg D₀ hs).trans
      (((std_fold_map leftRead readIn ((u.product v).product s))).symm.trans
        (congrArg D₀ (tripleRetag_word u (fun _ => v) (fun _ _ => s)))).symm
  have ek := tripleIndependentCell_assoc R L NR NL A B D u v s
    (p x h₀.1) (q y h₁.1) (r w h₁.2) P Q hl hr
  have prep : HEq (readCell t ht ≫ β) (P₀ ≫ β) :=
    structural_seq_heq (K:=coeff (C:=C)) hEq rfl rfl hL HEq.rfl
  have ha : HEq (act 𝒮 Zₐ α F) (act 𝒮 Zₐ α (u.product (v.product s))) := by
    have helper {x y : List (X × Y × W)} (h : x = y) :
        HEq (act 𝒮 Zₐ α x) (act 𝒮 Zₐ α y) := by subst y; rfl
    exact helper hs
  have finish : HEq (act 𝒮 Zₐ α F ≫ rCell t ht) (act 𝒮 Zₐ α (u.product (v.product s)) ≫ P₁) :=
    structural_seq_heq (K:=coeff (C:=C)) (congrArg D₀ hs) (congrArg D₁ hs) rfl ha hR
  exact eq_of_heq (prep.trans (ek.trans finish.symm))


section Square
variable {I : C} (J : UnitCompat R I) (U : AssocRightUnit R J P)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))
variable (hx : xs.Nodup) (hy : ys.Nodup) (hw : ws.Nodup)
variable (ax : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (ay : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (aw : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D ws ⟶ I)
variable (bx : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A' xs' ⟶ I)
variable (by' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B' ys' ⟶ I)
variable (bw : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D' ws' ⟶ I)
local notation "assocX" => independentAssocIso R L J P NR NL Q U A B D xs ys ws ax ay aw hl hr ι
  (nodup_product_word hx (nodup_product_word hy hw))
local notation "assocY" => independentAssocIso R L J P NR NL Q U A' B' D' xs' ys' ws' bx by' bw hl hr ι
  (nodup_product_word hx' (nodup_product_word hy' hw'))
local notation "originalL" => independentNativeWordMap T (independentNativeWordMap T pNative qNative R L) rNative R L
local notation "originalR" => independentNativeWordMap T pNative (independentNativeWordMap T qNative rNative R L) R L

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4600000 in
theorem independentAssoc_original_native_square :
    (originalL).comp (assocY).hom.native = (assocX).hom.native.comp originalR := by
  let hf₀ := wordProduct_support (Prod.map f g) k (wordProduct_support f g hf hg) hk
  let hfr := wordProduct_support f (Prod.map g k) hf (wordProduct_support g k hg hk)
  let hfl := nodup_product_word (nodup_product_word hx' hy') hw'
  let hu := nodup_product_word hx (nodup_product_word hy hw)
  let hv := nodup_product_word hx' (nodup_product_word hy' hw')
  let hp := retag_word_support readIn readOut fl fr (fun _ => rfl) readIn_word readOut_word hf₀
  let e := wordNativeMap fr hp hv leftRead leftRead' (fun j => readCell wr'[j] (List.getElem_mem _))
  let j := wordNativeMap fr hfr hv ar ar' (fun j => rCell wr'[j] (List.getElem_mem _))
  let α (z : X × Y × W) : leftRead z ≅ ar z := by
    let _ := ι (A z.1) (B z.2.1) (D z.2.2)
    exact asIso (P.assoc (A z.1) (B z.2.1) (D z.2.2))
  let β (z : X' × Y' × W') : leftRead' z ≅ ar' z := by
    let _ := ι (A' z.1) (B' z.2.1) (D' z.2.2)
    exact asIso (P.assoc (A' z.1) (B' z.2.1) (D' z.2.2))
  have h := wordNativeMap_identChart_square fr hp hu hv leftRead ar leftRead' ar' α β readCell rCell
    (independentTripleCell_square R L A B D A' B' D' f g k p q r P NR NL Q hl hr)
  rw [wordReindex_ident_pointwise, wordReindex_ident_pointwise] at h
  have HH : HEq originalL e :=
    (independentTripleLeftMap_heq R L A B D A' B' D' f g k hf hg hk hx' hy' hw' p q r).trans
      (retagWordMap_heq readIn readOut fl fr (fun _ => rfl) readIn_word readOut_word leftRead leftRead' lCell hf₀ hfl hv)
  have KK : HEq originalR j :=
    independentTripleRightMap_heq R L A B D A' B' D' f g k hf hg hk hx' hy' hw' p q r
  have s₀ : (independentFamily T (independentFamily T (wordFamily A xs) (wordFamily B ys)) (wordFamily D ws)) =
        wordFamily leftRead wr := by
    rw [independentFamily_word, independentFamily_word]
    exact wordFamily_read_eq leftRead readIn wl wr readIn_word
  have s₁ : (independentFamily T (independentFamily T (wordFamily A' xs') (wordFamily B' ys')) (wordFamily D' ws')) =
        wordFamily leftRead' wr' := by
    rw [independentFamily_word, independentFamily_word]
    exact wordFamily_read_eq leftRead' readOut wl' wr' readOut_word
  have t₀ : (independentFamily T (wordFamily A xs) (independentFamily T (wordFamily B ys) (wordFamily D ws))) =
        wordFamily ar wr := by rw [independentFamily_word, independentFamily_word]
  have t₁ : (independentFamily T (wordFamily A' xs') (independentFamily T (wordFamily B' ys') (wordFamily D' ws'))) =
        wordFamily ar' wr' := by rw [independentFamily_word, independentFamily_word]
  have hh₀ := independentAssocIso_pointwise_heq R L J P NR NL Q U A B D xs ys ws ax ay aw hl hr ι hu
  have hh₁ := independentAssocIso_pointwise_heq R L J P NR NL Q U A' B' D' xs' ys' ws' bx by' bw hl hr ι hv
  exact eq_of_heq ((nativeHom_comp_heq originalL (assocY).hom.native e _ s₀ s₁ t₁ HH hh₁).trans
    ((heq_of_eq h).trans (nativeHom_comp_heq (assocX).hom.native originalR _ j s₀ t₀ t₁ hh₀ KK).symm))


variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (xp : (wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _))).comp (wordAug A' xs' bx).ε = (wordAug A xs ax).ε)
variable (yp : (wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))).comp (wordAug B' ys' by').ε = (wordAug B ys ay).ε)
variable (wp : (wordNativeMap k hk hw' D D' (fun j => r ws'[j] (List.getElem_mem _))).comp (wordAug D' ws' bw).ε = (wordAug D ws aw).ε)
set_option quotPrecheck false in
local notation "Pₐ" => (⟨pNative,xp⟩ : AugHom ℙ (wordAug A xs ax) (wordAug A' xs' bx))
set_option quotPrecheck false in
local notation "Qₐ" => (⟨qNative,yp⟩ : AugHom ℙ (wordAug B ys ay) (wordAug B' ys' by'))
set_option quotPrecheck false in
local notation "Rₐ" => (⟨rNative,wp⟩ : AugHom ℙ (wordAug D ws aw) (wordAug D' ws' bw))
set_option quotPrecheck false in
local notation "indMap" => independentAugMap R L (J.ρ I) N NR NL hl hr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- The actual independent associator is natural on all input carrier
maps with arbitrary whole fibre cells preserving their augmentations. -/
theorem independentAssoc_original_augmented_square :
    (indMap (indMap Pₐ Qₐ) Rₐ).comp (assocY).hom =
      (assocX).hom.comp (indMap Pₐ (indMap Qₐ Rₐ)) := by
  apply AugHom.ext
  exact independentAssoc_original_native_square R L A B D A' B' D' f g k hf hg hk hx' hy' hw' p q r
    P NR NL Q hl hr J U ι hx hy hw ax ay aw bx by' bw

end Square
end Triple

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
