module
public import ContextualComposition.NativeBinaryFubiniTrace
@[expose] public section

/-! Whiskering compatible structural comparisons in both dependent
slots, while reading both original address alphabets. -/
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
variable (J : UnitCompat R I) (NL : GatherLeftNat L)

variable {X Y X' Y' : Type u} {A : X → C} {B : X' → C} {D : X → Y → C} {E : X' → Y' → C}
variable (f : X → X') (g : X → Y → Y')
variable (xs : List X) (xs' : List X') (ys : X → List Y) (ys' : X' → List Y')
variable (u₀ : xs.map f = xs') (u₁ : ∀ x, (ys x).map (g x) = ys' (f x))
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B xs' ⟶ I)
variable (d : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x) (ys x) ⟶ I)
variable (e : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (E x) (ys' x) ⟶ I)
variable (p : ∀ x, A x ≅ B (f x)) (q : ∀ x y, D x y ≅ E (f x) (g x y))
variable (hp : act (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (fun x => (p x).hom) xs ≫
  eqToHom ((std_fold_map B f xs).symm.trans (congrArg (fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B) u₀)) ≫ b = a)
variable (hq : ∀ x, act (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (fun y => (q x y).hom) (ys x) ≫
  eqToHom ((std_fold_map (E (f x)) (g x) (ys x)).symm.trans
    (congrArg (fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (E (f x))) (u₁ x))) ≫ e (f x) = d x)

include u₀ u₁ in
theorem dependentBothRetag_word :
    (dependentWord xs ys).map (fun z => (f z.1,g z.1 z.2)) = dependentWord xs' ys' := by
  subst xs'
  unfold dependentWord
  simp only [List.map_flatMap, List.flatMap_map, List.map_map]
  apply congrArg (fun k => xs.flatMap k)
  funext x
  rw [← u₁ x, List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def dependentBothRetagIso (hn : (dependentWord xs ys).Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J xs ys A D (indexedAugmentation d) a)
      (dependentWordAug R L J xs' ys' B E (indexedAugmentation e) b) := by
  let v := (std_fold_map B f xs).symm.trans (congrArg (fold 𝒮 Zₐ B) u₀)
  let η := fun x => (std_fold_map (E (f x)) (g x) (ys x)).symm.trans
    (congrArg (fold 𝒮 Zₐ (E (f x))) (u₁ x))
  let β := eqToHom v ≫ b
  let δ := fun x => eqToHom (η x) ≫ e (f x)
  let u := dependentWhiskerIso R L J NL xs ys p q a β d δ hp hq hn
  have s₀ := dependentAug_child_read R L J g xs ys (ys' ∘ f) u₁ β (fun x => e (f x))
  have s₁ := dependentAug_parent_read R L J f xs xs' u₀ ys' b e
  exact u.retarget rfl (s₀.trans s₁)

set_option backward.isDefEq.respectTransparency false in
theorem dependentBothRetagIso_pointwise (hn : (dependentWord xs ys).Nodup) :
    HEq (dependentBothRetagIso R L J NL f g xs xs' ys ys' u₀ u₁ a b d e p q hp hq hn).hom.native
      (wordPointwise (dependentWord xs ys) (fun z => T.map (p z.1).hom (q z.1 z.2).hom)) := by
  unfold dependentBothRetagIso
  dsimp only
  exact (NativeAugmentedIso.retarget_native_heq _ _ _).trans
    (heq_of_eq (dependentWhiskerIso_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))


set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_trace {Γ : Type u} {F G : Γ → C} (w : List Γ) (hn : w.Nodup)
    (p : ∀ z, F z ⟶ G z) :
    RawSingletonTrace (rawWordFrame F w hn) (rawWordFrame G w hn) p (wordPointwise w p) := by
  exact ⟨Equiv.refl _, fun j => p w[j], rfl, fun _ => rfl, fun _ => HEq.rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2100000 in
theorem dependentBothRetagIso_trace {Ω : Type u}
    (hn : (dependentWord xs ys).Nodup) (hn' : (dependentWord xs' ys').Nodup)
    (readIn : X × Y → Ω) (readOut : X' × Y' → Ω)
    (i₀ : Function.Injective readIn) (i₁ : Function.Injective readOut)
    (coh : ∀ z, readIn z = readOut (f z.1,g z.1 z.2))
    (F G : Ω → C) (eF : ∀ z, dependentLabels (T:=T) A D z = F (readIn z))
    (eG : ∀ z, dependentLabels (T:=T) B E z = G (readOut z))
    (m : ∀ z, F z ⟶ G z)
    (h : ∀ z : X × Y, HEq (T.map (p z.1).hom (q z.1 z.2).hom) (m (readIn z))) :
    RawSingletonTrace ((rawWordFrame (dependentLabels (T:=T) A D) (dependentWord xs ys) hn).relabel readIn i₀ F eF)
      ((rawWordFrame (dependentLabels (T:=T) B E) (dependentWord xs' ys') hn').relabel readOut i₁ G eG)
      m (dependentBothRetagIso R L J NL f g xs xs' ys ys' u₀ u₁ a b d e p q hp hq hn).hom.native := by
  let j := fun z : X × Y => (f z.1,g z.1 z.2)
  let w := dependentWord xs ys
  let w' := dependentWord xs' ys'
  let A₀ := dependentLabels (T:=T) A D
  let B₀ := dependentLabels (T:=T) B E
  let k := fun z : X × Y => T.map (p z.1).hom (q z.1 z.2).hom
  let v := dependentBothRetagIso R L J NL f g xs xs' ys ys' u₀ u₁ a b d e p q hp hq hn
  have a₀ : ∀ z : X × Y, (B₀ ∘ j) z = G (readIn z) := fun z =>
    (eG (j z)).trans (congrArg G (coh z).symm)
  have W : w.map j = w' := dependentBothRetag_word f g xs xs' ys ys' u₀ u₁
  let m₀ := (wordPointwise_trace (F:=A₀) (G:=B₀ ∘ j) w hn k).relabel readIn i₀ F G eF a₀ m h
  let E' := wordFamily_read_eq B₀ j w w' W
  have m₁ : HEq (wordPointwise w k) v.hom.native :=
    (dependentBothRetagIso_pointwise R L J NL f g xs xs' ys ys' u₀ u₁ a b d e p q hp hq hn).symm
  apply m₀.retarget rfl E' m₁ (fun _ => rfl) ?_ (fun _ => HEq.rfl)
  intro i
  change readIn w[i] = readOut w'[Fin.cast (congrArg Family.n E') i]
  exact (coh w[i]).trans (congrArg readOut (rawWordFrame_read_cast B₀ j w w' W i))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
