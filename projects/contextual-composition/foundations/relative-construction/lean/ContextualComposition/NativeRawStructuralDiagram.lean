module
public import ContextualComposition.NativeDependentStructural
@[expose] public section

/-! Exact interpretation of structural diagrams on a common raw word.
Native arrows still use the actual ordered singleton preimage. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

noncomputable def wordPointwise {X : Type w} {A B : X → C} (xs : List X)
    (p : ∀ x, A x ⟶ B x) : Hom ℙ (wordFamily A xs) (wordFamily B xs) :=
  nativeSingletonMap (A:=wordFamily A xs) (B:=wordFamily B xs) (Equiv.refl (Fin xs.length)) (fun j => p xs[j])

set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_id {X : Type w} (A : X → C) (xs : List X) :
    wordPointwise xs (fun x => 𝟙 (A x)) = Hom.ident (wordFamily A xs) :=
  nativeSingletonMap_ident _

set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_comp {X : Type w} {A B D : X → C} (xs : List X)
    (p : ∀ x, A x ⟶ B x) (q : ∀ x, B x ⟶ D x) :
    (wordPointwise xs p).comp (wordPointwise xs q) = wordPointwise xs (fun x => p x ≫ q x) := by
  unfold wordPointwise
  rw [nativeSingletonMap_comp]
  apply nativeSingletonMap_congr
  · intro j
    rfl
  · intro j
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_eq_of_mem {X : Type w} {A B : X → C} (xs : List X)
    (p q : ∀ x, A x ⟶ B x) (h : ∀ x ∈ xs, p x = q x) :
    wordPointwise xs p = wordPointwise xs q := by
  unfold wordPointwise
  apply congrArg (nativeSingletonMap (A:=wordFamily A xs) (B:=wordFamily B xs) (Equiv.refl (Fin xs.length)))
  funext j
  exact h _ (List.getElem_mem _)

set_option backward.isDefEq.respectTransparency false in
theorem wordEquiv_ident_chart {X : Type w} (xs : List X) (h : xs.Nodup) :
    wordEquiv (AddressOrder.ident xs).perm h = Equiv.refl _ := by
  apply Equiv.ext
  intro j
  exact Fin.ext (h.getElem_inj.mp (wordEquiv_get _ _ j))

set_option backward.isDefEq.respectTransparency false in
theorem wordReindex_ident_pointwise {X : Type u} {A B : X → C}
    (xs : List X) (hn : xs.Nodup) (φ : ∀ x, A x ≅ B x) :
    nativeReindex (A:=wordFamily A xs) (B:=wordFamily B xs)
      (wordEquiv (AddressOrder.ident xs).perm hn) (wordComparisonCells A B (.ident xs) hn φ) =
      wordPointwise xs (fun x => (φ x).hom) := by
  unfold wordPointwise
  rw [nativeReindex_singleton]
  apply nativeSingletonMap_congr
  · intro j
    exact congrFun (congrArg DFunLike.coe (wordEquiv_ident_chart xs hn)) j
  · intro j
    change HEq
      (eqToHom (congrArg A (wordEquiv_get_symm (AddressOrder.ident xs).perm hn j)) ≫ (φ xs[j]).hom)
      ((φ xs[j]).hom)
    exact hom_source_pin_heq _ _

set_option backward.isDefEq.respectTransparency false in
theorem wordAugIso_ident_pointwise {X : Type u} {A B : X → C} {I : C}
    (xs : List X) (hn : xs.Nodup) (φ : ∀ x, A x ≅ B x)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B xs ⟶ I)
    (h : AddressOrder.mapSum additiveStructure A (.ident xs) ≫ act 𝒮 Zₐ (fun y => (φ y).hom) xs ≫ b = a) :
    (wordAugIso A B (.ident xs) hn φ a b h).hom.native = wordPointwise xs (fun x => (φ x).hom) :=
  wordReindex_ident_pointwise xs hn φ

/-- A pointwise coefficient diagram over a common structural presentation
is a diagram of actual augmented native arrows. -/
theorem wordAugIso_pointwise_paste {X : Type u} {A B D : X → C} {I : C}
    (xs : List X) (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B xs ⟶ I)
    (c : fold 𝒮 Zₐ D xs ⟶ I)
    (e : AugHom ℙ (wordAug A xs a) (wordAug B xs b))
    (f : AugHom ℙ (wordAug B xs b) (wordAug D xs c))
    (g : AugHom ℙ (wordAug A xs a) (wordAug D xs c))
    (p : ∀ x, A x ⟶ B x) (q : ∀ x, B x ⟶ D x) (r : ∀ x, A x ⟶ D x)
    (he : e.native = wordPointwise xs p) (hf : f.native = wordPointwise xs q)
    (hg : g.native = wordPointwise xs r)
    (h : ∀ x ∈ xs, p x ≫ q x = r x) :
    e.comp f = g := by
  apply AugHom.ext
  change e.native.comp f.native = g.native
  rw [he,hf,hg]
  exact (wordPointwise_comp xs p q).trans (wordPointwise_eq_of_mem xs _ _ h)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
