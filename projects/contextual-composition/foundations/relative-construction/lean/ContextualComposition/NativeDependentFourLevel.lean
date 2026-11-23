module
public import ContextualComposition.NativeDependentRetagWhisker
@[expose] public section

/-! The five actual four-level bracketings and their five augmented
associator edges. Raw leaves retain the address in each of the four
families, including when different leaves carry equal coefficients. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {X Y W Z : Type u} {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (xs : List X) (ys : X → List Y) (ws : X → Y → List W) (zs : X → Y → W → List Z)
variable (A : X → C) (B : X → Y → C) (D : X → Y → W → C) (E : X → Y → W → Z → C)
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I)
variable (d : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ I)
variable (e : ∀ x y w, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (E x y w) (zs x y w) ⟶ I)

local notation "abWord" => dependentWord xs ys
local notation "abLab" => dependentLabels (T:=T) A B
local notation "bcWord" => (fun x => dependentWord (ys x) (ws x))
local notation "bcLab" => (fun x => dependentLabels (T:=T) (B x) (D x))
local notation "cdWord" => (fun x y => dependentWord (ws x y) (zs x y))
local notation "cdLab" => (fun x y => dependentLabels (T:=T) (D x y) (E x y))
local notation "abCell" => dependentWordAugCell R L J xs ys A B (indexedAugmentation b) a
local notation "bcCell" => (fun x => dependentWordAugCell R L J (ys x) (ws x) (B x) (D x) (indexedAugmentation (d x)) (b x))
local notation "cdCell" => (fun x y => dependentWordAugCell R L J (ws x y) (zs x y) (D x y) (E x y) (indexedAugmentation (e x y)) (d x y))

noncomputable def fourLeft : Aug ℙ I :=
  dependentAssocLeft R L J abWord (fun p => ws p.1 p.2) (fun p => zs p.1 p.2)
    abLab (fun p => D p.1 p.2) (fun p => E p.1 p.2) abCell (fun p => d p.1 p.2) (fun p => e p.1 p.2)

noncomputable def fourTop : Aug ℙ I :=
  dependentAssocLeft R L J xs bcWord (fun x p => zs x p.1 p.2) A bcLab
    (fun x p => E x p.1 p.2) a bcCell (fun x p => e x p.1 p.2)

noncomputable def fourMiddle : Aug ℙ I :=
  dependentAssocRight R L J xs bcWord (fun x p => zs x p.1 p.2) A bcLab
    (fun x p => E x p.1 p.2) a bcCell (fun x p => e x p.1 p.2)

noncomputable def fourRight : Aug ℙ I :=
  dependentAssocRight R L J xs ys cdWord A B cdLab a b cdCell

noncomputable def fourBottom : Aug ℙ I :=
  dependentAssocLeft R L J xs ys cdWord A B cdLab a b cdCell

variable (P : TensorPrimitive T)
variable (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (ι : ∀ a b c, IsIso (P.assoc a b c))

set_option backward.isDefEq.respectTransparency false in
noncomputable def fourEdgeLT
    (hn : (dependentWord (dependentWord abWord (fun p => ws p.1 p.2))
      (fun p => zs p.1.1 p.1.2 p.2)).Nodup) :
    NativeAugmentedIso (fourLeft R L J xs ys ws zs A B D E a b d e)
      (fourTop R L J xs ys ws zs A B D E a b d e) := by
  let p (t : (X × Y) × W) : assocLeftLabels T A B D t ≅ assocRightLabels T A B D (tripleRetag t) := by
    let _ := ι (A t.1.1) (B t.1.1 t.1.2) (D t.1.1 t.1.2 t.2)
    exact asIso (P.assoc (A t.1.1) (B t.1.1 t.1.2) (D t.1.1 t.1.2 t.2))
  exact dependentParentWhiskerIso R L J NL tripleRetag
    (dependentWord abWord (fun p => ws p.1 p.2)) (dependentWord xs bcWord)
    (tripleRetag_word xs ys ws) (fun t => zs t.1 t.2.1 t.2.2) p
    (dependentAssocLeftAug R L J xs ys ws A B D a b d)
    (dependentAssocRightAug R L J xs ys ws A B D a b d)
    (fun t => e t.1 t.2.1 t.2.2)
    (dependentAssoc_preserves_pullback R L J P NL Q U hl xs ys ws A B D a b d) hn

set_option backward.isDefEq.respectTransparency false in
noncomputable def fourEdgeTM
    (hn : (dependentWord xs (fun x => dependentWord (bcWord x) (fun p => zs x p.1 p.2))).Nodup) :
    NativeAugmentedIso (fourTop R L J xs ys ws zs A B D E a b d e)
      (fourMiddle R L J xs ys ws zs A B D E a b d e) :=
  dependentAssocIso R L J P NL Q U xs bcWord (fun x p => zs x p.1 p.2) A bcLab
    (fun x p => E x p.1 p.2) a bcCell (fun x p => e x p.1 p.2) hl ι hn

set_option backward.isDefEq.respectTransparency false in
noncomputable def fourEdgeMR
    (hn : (dependentWord xs (fun x => dependentWord (bcWord x) (fun p => zs x p.1 p.2))).Nodup) :
    NativeAugmentedIso (fourMiddle R L J xs ys ws zs A B D E a b d e)
      (fourRight R L J xs ys ws zs A B D E a b d e) := by
  let q (x : X) (t : (Y × W) × Z) :
      assocLeftLabels T (B x) (D x) (E x) t ≅ assocRightLabels T (B x) (D x) (E x) (tripleRetag t) := by
    let _ := ι (B x t.1.1) (D x t.1.1 t.1.2) (E x t.1.1 t.1.2 t.2)
    exact asIso (P.assoc (B x t.1.1) (D x t.1.1 t.1.2) (E x t.1.1 t.1.2 t.2))
  exact dependentChildWhiskerIso R L J NL (fun _ => tripleRetag) xs
    (fun x => dependentWord (bcWord x) (fun p => zs x p.1 p.2))
    (fun x => dependentWord (ys x) (cdWord x))
    (fun x => tripleRetag_word (ys x) (ws x) (zs x)) q a
    (fun x => dependentAssocLeftAug R L J (ys x) (ws x) (zs x) (B x) (D x) (E x) (b x) (d x) (e x))
    (fun x => dependentAssocRightAug R L J (ys x) (ws x) (zs x) (B x) (D x) (E x) (b x) (d x) (e x))
    (fun x => dependentAssoc_preserves_pullback R L J P NL Q U hl (ys x) (ws x) (zs x)
      (B x) (D x) (E x) (b x) (d x) (e x)) hn

set_option backward.isDefEq.respectTransparency false in
noncomputable def fourEdgeLB
    (hn : (dependentWord abWord (fun p => cdWord p.1 p.2)).Nodup) :
    NativeAugmentedIso (fourLeft R L J xs ys ws zs A B D E a b d e)
      (fourBottom R L J xs ys ws zs A B D E a b d e) :=
  dependentAssocIso R L J P NL Q U abWord (fun p => ws p.1 p.2) (fun p => zs p.1 p.2)
    abLab (fun p => D p.1 p.2) (fun p => E p.1 p.2) abCell (fun p => d p.1 p.2) (fun p => e p.1 p.2) hl ι hn

set_option backward.isDefEq.respectTransparency false in
noncomputable def fourEdgeBR
    (hn : (dependentWord xs (fun x => dependentWord (ys x) (cdWord x))).Nodup) :
    NativeAugmentedIso (fourBottom R L J xs ys ws zs A B D E a b d e)
      (fourRight R L J xs ys ws zs A B D E a b d e) :=
  dependentAssocIso R L J P NL Q U xs ys cdWord A B cdLab a b cdCell hl ι hn


section Raw
def fourReadL (z : ((X × Y) × W) × Z) : X × Y × W × Z :=
  (z.1.1.1,z.1.1.2,z.1.2,z.2)
def fourReadT (z : (X × (Y × W)) × Z) : X × Y × W × Z :=
  (z.1.1,z.1.2.1,z.1.2.2,z.2)
def fourReadM (z : X × ((Y × W) × Z)) : X × Y × W × Z :=
  (z.1,z.2.1.1,z.2.1.2,z.2.2)
def fourReadB (z : (X × Y) × (W × Z)) : X × Y × W × Z :=
  (z.1.1,z.1.2,z.2.1,z.2.2)

set_option quotPrecheck false in
local notation "wR" => dependentWord xs (fun x => dependentWord (ys x) (cdWord x))
set_option quotPrecheck false in
local notation "wL" => dependentWord (dependentWord abWord (fun p => ws p.1 p.2)) (fun p => zs p.1.1 p.1.2 p.2)
set_option quotPrecheck false in
local notation "wT" => dependentWord (dependentWord xs bcWord) (fun p => zs p.1 p.2.1 p.2.2)
set_option quotPrecheck false in
local notation "wM" => dependentWord xs (fun x => dependentWord (bcWord x) (fun p => zs x p.1 p.2))
set_option quotPrecheck false in
local notation "wB" => dependentWord abWord (fun p => cdWord p.1 p.2)

theorem fourReadL_word : (wL).map fourReadL = wR := by
  simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc]
  rfl

theorem fourReadT_word : (wT).map fourReadT = wR := by
  simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc]
  rfl

theorem fourReadM_word : (wM).map fourReadM = wR := by
  simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc]
  rfl

theorem fourReadB_word : (wB).map fourReadB = wR := by
  simp only [dependentWord, List.map_flatMap, List.flatMap_map, List.map_map, List.flatMap_assoc]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- The actual augmented dependent associator satisfies the pentagon.
Each edge is formed independently on its literal bracketed input; the
four raw addresses are identified only through their ordered readings. -/
theorem actual_dependent_augmented_pentagon
    (hL : (wL).Nodup) (hM : (wM).Nodup) (hB : (wB).Nodup) (hR : (wR).Nodup)
    (hP : MulPentagon P) :
    (((fourEdgeLT R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hL).hom.comp
      (fourEdgeTM R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hM).hom).comp
      (fourEdgeMR R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hM).hom) =
    ((fourEdgeLB R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hB).hom.comp
      (fourEdgeBR R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hR).hom) := by
  let p := (fourEdgeLT R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hL).hom
  let q := (fourEdgeTM R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hM).hom
  let r := (fourEdgeMR R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hM).hom
  let s := (fourEdgeLB R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hB).hom
  let t := (fourEdgeBR R L J xs ys ws zs A B D E a b d e P NL Q U hl ι hR).hom
  let A₀ (z : X × Y × W × Z) := A z.1
  let B₀ (z : X × Y × W × Z) := B z.1 z.2.1
  let D₀ (z : X × Y × W × Z) := D z.1 z.2.1 z.2.2.1
  let E₀ (z : X × Y × W × Z) := E z.1 z.2.1 z.2.2.1 z.2.2.2
  let AL := fun z => T.obj (T.obj (T.obj (A₀ z) (B₀ z)) (D₀ z)) (E₀ z)
  let AT := fun z => T.obj (T.obj (A₀ z) (T.obj (B₀ z) (D₀ z))) (E₀ z)
  let AM := fun z => T.obj (A₀ z) (T.obj (T.obj (B₀ z) (D₀ z)) (E₀ z))
  let AR := fun z => T.obj (A₀ z) (T.obj (B₀ z) (T.obj (D₀ z) (E₀ z)))
  let AB := fun z => T.obj (T.obj (A₀ z) (B₀ z)) (T.obj (D₀ z) (E₀ z))
  let p₀ (z) : AL z ⟶ AT z := T.map (P.assoc (A₀ z) (B₀ z) (D₀ z)) (𝟙 (E₀ z))
  let q₀ (z) : AT z ⟶ AM z := P.assoc (A₀ z) (T.obj (B₀ z) (D₀ z)) (E₀ z)
  let r₀ (z) : AM z ⟶ AR z := T.map (𝟙 (A₀ z)) (P.assoc (B₀ z) (D₀ z) (E₀ z))
  let s₀ (z) : AL z ⟶ AB z := P.assoc (T.obj (A₀ z) (B₀ z)) (D₀ z) (E₀ z)
  let t₀ (z) : AB z ⟶ AR z := P.assoc (A₀ z) (B₀ z) (T.obj (D₀ z) (E₀ z))
  have hAL : (fourLeft R L J xs ys ws zs A B D E a b d e).base = wordFamily AL wR :=
    wordFamily_read_eq AL fourReadL wL wR (fourReadL_word xs ys ws zs)
  have hAT : (fourTop R L J xs ys ws zs A B D E a b d e).base = wordFamily AT wR :=
    wordFamily_read_eq AT fourReadT wT wR (fourReadT_word xs ys ws zs)
  have hAM : (fourMiddle R L J xs ys ws zs A B D E a b d e).base = wordFamily AM wR :=
    wordFamily_read_eq AM fourReadM wM wR (fourReadM_word xs ys ws zs)
  have hAR : (fourRight R L J xs ys ws zs A B D E a b d e).base = wordFamily AR wR := rfl
  have hAB : (fourBottom R L J xs ys ws zs A B D E a b d e).base = wordFamily AB wR :=
    wordFamily_read_eq AB fourReadB wB wR (fourReadB_word xs ys ws zs)
  have hp : HEq p.native (wordPointwise wL (fun z => p₀ (fourReadL z))) := by
    unfold p fourEdgeLT
    dsimp only
    exact dependentParentWhiskerIso_pointwise R L J NL _ _ _ _ _ _ _ _ _ _ _
  have hq : HEq q.native (wordPointwise wM (fun z => q₀ (fourReadM z))) := by
    unfold q fourEdgeTM
    exact dependentAssocIso_pointwise_heq R L J P NL Q U hl _ _ _ _ _ _ _ _ _ ι hM
  have hr : HEq r.native (wordPointwise wM (fun z => r₀ (fourReadM z))) := by
    unfold r fourEdgeMR
    dsimp only
    exact dependentChildWhiskerIso_pointwise R L J NL _ _ _ _ _ _ _ _ _ _ _
  have hs : HEq s.native (wordPointwise wB (fun z => s₀ (fourReadB z))) := by
    unfold s fourEdgeLB
    exact dependentAssocIso_pointwise_heq R L J P NL Q U hl _ _ _ _ _ _ _ _ _ ι hB
  have ht : HEq t.native (wordPointwise wR t₀) := by
    unfold t fourEdgeBR
    exact dependentAssocIso_pointwise_heq R L J P NL Q U hl _ _ _ _ _ _ _ _ _ ι hR
  change (p.comp q).comp r = s.comp t
  exact AugHom.pentagon_of_pointwise_native_heq wR hAL hAT hAM hAR hAB p q r s t
    (hp.trans (wordPointwise_retag_heq fourReadL wL wR (fourReadL_word xs ys ws zs) p₀))
    (hq.trans (wordPointwise_retag_heq fourReadM wM wR (fourReadM_word xs ys ws zs) q₀))
    (hr.trans (wordPointwise_retag_heq fourReadM wM wR (fourReadM_word xs ys ws zs) r₀))
    (hs.trans (wordPointwise_retag_heq fourReadB wB wR (fourReadB_word xs ys ws zs) s₀)) ht
    (fun z _ => hP (A₀ z) (B₀ z) (D₀ z) (E₀ z))

end Raw

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
