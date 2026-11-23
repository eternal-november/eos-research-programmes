module
public import ContextualComposition.NativeDependentOrderWhisker
@[expose] public section

/-! The general ordered-read form of dependent structural whiskering.
Coordinate changes and permutation of the resulting ordered words are
explicit and have distinct proof obligations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
set_option quotPrecheck false in
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
set_option quotPrecheck false in
local notation "Zₐ" => 𝟙_ C
set_option quotPrecheck false in
local notation "ℙ" => standardPush (C:=C)

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem equiv_word_read {X Y : Type u} (g : X ≃ Y) (ys : List Y) :
    (ys.map g.symm).map g = ys := by
  simp only [List.map_map]
  have h : (g : X → Y) ∘ g.symm = id := funext g.apply_symm_apply
  rw [h, List.map_id]

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (NL : GatherLeftNat L)
variable {X Y X' Y' : Type u} {A : X → C} {B : X' → C} {D : X → Y → C} {E : X' → Y' → C}
variable (f : X ≃ X') (g : X → Y ≃ Y')
variable {xs : List X} {xs' : List X'} {ys : X → List Y} {ys' : X' → List Y'}
variable (o : AddressOrder X xs (xs'.map f.symm))
variable (q : ∀ x, AddressOrder Y (ys x) ((ys' (f x)).map (g x).symm))
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B xs' ⟶ I)
variable (d : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x) (ys x) ⟶ I)
variable (e : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (E x) (ys' x) ⟶ I)
variable (φ : ∀ x, A x ≅ B (f x)) (ψ : ∀ x y, D x y ≅ E (f x) (g x y))
variable [lF : ∀ x, (leftFactor T (B x)).LaxBraided]
variable (hl : ∀ x, SameLeftGather T (B x) L)
set_option quotPrecheck false in
local notation "xs₀" => xs'.map f.symm
set_option quotPrecheck false in
local notation "ys₀" => (fun x => (ys' (f x)).map (g x).symm)
set_option quotPrecheck false in
local notation "aPin" => (std_fold_map B f xs₀).symm.trans
  (congrArg (fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B) (equiv_word_read f xs'))
set_option quotPrecheck false in
local notation "dPin" => (fun x => (std_fold_map (E (f x)) (g x) (ys₀ x)).symm.trans
  (congrArg (fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (E (f x))) (equiv_word_read (g x) (ys' (f x)))))

set_option backward.isDefEq.respectTransparency false in
omit lF in
theorem dependentReadBack_eq :
    dependentWordAug R L J xs₀ ys₀ (B ∘ f) (fun x y => E (f x) (g x y))
      (indexedAugmentation (fun x => eqToHom (dPin x) ≫ e (f x))) (eqToHom aPin ≫ b) =
    dependentWordAug R L J xs' ys' B E (indexedAugmentation e) b := by
  have s₀ := dependentAug_child_read R L J (fun x y => g x y) xs₀ ys₀ (ys' ∘ f)
    (fun x => equiv_word_read (g x) (ys' (f x))) (eqToHom aPin ≫ b) (fun x => e (f x))
  exact s₀.trans (dependentAug_parent_read R L J f xs₀ xs' (equiv_word_read f xs') ys' b e)

set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentOrderedReadIso
    (hp : AddressOrder.mapSum additiveStructure A o ≫ act 𝒮 Zₐ (fun x => (φ x).hom) xs₀ ≫
      eqToHom aPin ≫ b = a)
    (hq : ∀ x, AddressOrder.mapSum additiveStructure (D x) (q x) ≫
      act 𝒮 Zₐ (fun y => (ψ x y).hom) (ys₀ x) ≫ eqToHom (dPin x) ≫ e (f x) = d x)
    (hn : (dependentWord xs ys).Nodup) :
    NativeAugmentedIso (dependentWordAug R L J xs ys A D (indexedAugmentation d) a)
      (dependentWordAug R L J xs' ys' B E (indexedAugmentation e) b) := by
  let _ (x : X) : (leftFactor T (B (f x))).LaxBraided := lF (f x)
  let v := dependentOrderIso R L J NL o q φ ψ a (eqToHom aPin ≫ b) d
    (fun x => eqToHom (dPin x) ≫ e (f x)) (fun x => hl (f x)) hp hq hn
  exact v.retarget rfl (dependentReadBack_eq R L J f g b e)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2700000 in
theorem dependentOrderedReadIso_trace {Ω : Type u}
    (hp : AddressOrder.mapSum additiveStructure A o ≫ act 𝒮 Zₐ (fun x => (φ x).hom) xs₀ ≫
      eqToHom aPin ≫ b = a)
    (hq : ∀ x, AddressOrder.mapSum additiveStructure (D x) (q x) ≫
      act 𝒮 Zₐ (fun y => (ψ x y).hom) (ys₀ x) ≫ eqToHom (dPin x) ≫ e (f x) = d x)
    (hn : (dependentWord xs ys).Nodup) (hn' : (dependentWord xs' ys').Nodup)
    (readIn : X × Y → Ω) (readOut : X' × Y' → Ω)
    (i₀ : Function.Injective readIn) (i₁ : Function.Injective readOut)
    (coh : ∀ z, readIn z = readOut (f z.1,g z.1 z.2))
    (F G : Ω → C) (eF : ∀ z, dependentLabels (T:=T) A D z = F (readIn z))
    (eG : ∀ z, dependentLabels (T:=T) B E z = G (readOut z))
    (m : ∀ z, F z ⟶ G z)
    (h : ∀ z : X × Y, HEq (T.map (φ z.1).hom (ψ z.1 z.2).hom) (m (readIn z))) :
    RawSingletonTrace ((rawWordFrame (dependentLabels (T:=T) A D) (dependentWord xs ys) hn).relabel readIn i₀ F eF)
      ((rawWordFrame (dependentLabels (T:=T) B E) (dependentWord xs' ys') hn').relabel readOut i₁ G eG)
      m (dependentOrderedReadIso R L J NL f g o q a b d e φ ψ hl hp hq hn).hom.native := by
  let _ (x : X) : (leftFactor T (B (f x))).LaxBraided := lF (f x)
  let k := fun z : X × Y => (f z.1,g z.1 z.2)
  let A₀ := dependentLabels (T:=T) A D
  let B₀ := dependentLabels (T:=T) B E
  let b₀ := eqToHom aPin ≫ b
  let d₀ := fun x => eqToHom (dPin x) ≫ e (f x)
  let u := dependentOrderIso R L J NL o q φ ψ a b₀ d d₀ (fun x => hl (f x)) hp hq hn
  let u₀ := dependentOrderedReadIso R L J NL f g o q a b d e φ ψ hl hp hq hn
  let v := dependentWord xs₀ ys₀
  let w := dependentWord xs' ys'
  let no := (dependentOrder o q).perm.nodup_iff.mp hn
  have W : v.map k = w := dependentBothRetag_word f (fun x y => g x y) xs₀ xs' ys₀ ys'
    (equiv_word_read f xs') (fun x => equiv_word_read (g x) (ys' (f x)))
  let e₀ := wordFamily_read_eq B₀ k v w W
  have a₀ : ∀ z : X × Y, (B₀ ∘ k) z = G (readIn z) := fun z =>
    (eG (k z)).trans (congrArg G (coh z).symm)
  have t := (dependentOrderIso_trace R L J NL o q φ ψ a b₀ d d₀ (fun x => hl (f x)) hp hq hn no).relabel
    readIn i₀ F G eF a₀ m h
  have E : HEq u.hom.native u₀.hom.native := by
    unfold u₀ dependentOrderedReadIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  apply t.retarget rfl e₀ E (fun _ => rfl) ?_ (fun _ => HEq.rfl)
  intro i
  change readIn v[i] = readOut w[Fin.cast (congrArg Family.n e₀) i]
  exact (coh v[i]).trans (congrArg readOut (rawWordFrame_read_cast B₀ k v w W i))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
