module
public import ContextualComposition.NativeIndependentSwap
@[expose] public section

/-! Realizing checked read comparisons as native augmentations, with
a coefficient trace in the source coordinates. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {I : C} {X Y : Type u} {A : X → C} {B : Y → C} {xs : List X} {ys : List Y}
variable {a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I}
variable {b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I}
variable (p : WordAugReadComparison A B xs ys a b)
set_option quotPrecheck false in
local notation "f" => p.read
set_option quotPrecheck false in
local notation "w" => ys.map (f).symm
set_option quotPrecheck false in
local notation "pin" => (std_fold_map B f w).symm.trans
  (congrArg (fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B) (equiv_word_read f ys))

set_option backward.isDefEq.respectTransparency false in
noncomputable def WordAugReadComparison.toIso
    (hn : xs.Nodup) : NativeAugmentedIso (wordAug A xs a) (wordAug B ys b) :=
  (wordAugIso A (B ∘ f) p.order hn p.coefficient a (eqToHom pin ≫ b) p.preserves).retarget rfl
    (wordAug_read_eq B f w ys (equiv_word_read f ys) _ _ (hom_source_pin_heq pin b))

set_option backward.isDefEq.respectTransparency false in
theorem WordAugReadComparison.toIso_trace (hn : xs.Nodup) (hm : ys.Nodup) :
    RawSingletonTrace (rawWordFrame A xs hn)
      ((rawWordFrame B ys hm).relabel (f).symm (f).symm.injective (B ∘ f)
        (fun x => congrArg B ((f).apply_symm_apply x).symm))
      (fun x => (p.coefficient x).hom) (p.toIso hn).hom.native := by
  let e := wordFamily_read_eq B f w ys (equiv_word_read f ys)
  let q := wordAugIso A (B ∘ f) p.order hn p.coefficient a (eqToHom pin ≫ b) p.preserves
  have H := wordAugIso_trace A (B ∘ f) p.order hn (p.order.perm.nodup_iff.mp hn)
    p.coefficient a (eqToHom pin ≫ b) p.preserves
  have K : HEq q.hom.native (p.toIso hn).hom.native := by
    unfold WordAugReadComparison.toIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  apply H.retarget rfl e K (fun _ => rfl) ?_ (fun _ => HEq.rfl)
  intro i
  change w[i] = (f).symm ys[Fin.cast (congrArg Family.n e) i]
  exact (f).injective ((rawWordFrame_read_cast B f w ys (equiv_word_read f ys) i).trans
    ((f).apply_symm_apply _).symm)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
