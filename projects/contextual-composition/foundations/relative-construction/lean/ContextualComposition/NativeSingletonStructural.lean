module
public import ContextualComposition.NativeDependentAssociatorNaturality
@[expose] public section

/-! Structural maps over carrier equivalences compose by their actual
singleton whole fibres in the native category. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

noncomputable def nativeSingletonMap {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, A.val (e.symm j) ⟶ B.val j) : Hom ℙ A B :=
  ⟨e, fun j => reindexSingleton e A.val j ≫ p j⟩

theorem nativeReindex_singleton {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, A.val (e.symm j) ≅ B.val j) :
    nativeReindex e p = nativeSingletonMap e (fun j => (p j).hom) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem nativeSingletonMap_ident (A : Family C) :
    nativeSingletonMap (A:=A) (B:=A) (Equiv.refl _) (fun j => 𝟙 (A.val j)) = Hom.ident A := by
  apply native_hom_iff_cell rfl _ _ |>.2
  intro j
  change (eqToHom (congrArg (fold 𝒮 Zₐ A.val) (equiv_fibreList (Equiv.refl _) j)) ≫ (ρ_ (A.val j)).hom) ≫ 𝟙 _ =
    𝟙 _ ≫ (eqToHom (congrArg (fold 𝒮 Zₐ A.val) (fibreList_id j)) ≫ (ρ_ (A.val j)).hom)
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem nativeSingletonMap_comp {A B D : Family C} (e : Fin A.n ≃ Fin B.n) (f : Fin B.n ≃ Fin D.n)
    (p : ∀ j, A.val (e.symm j) ⟶ B.val j) (q : ∀ j, B.val (f.symm j) ⟶ D.val j) :
    (nativeSingletonMap e p).comp (nativeSingletonMap f q) =
      nativeSingletonMap (e.trans f) (fun j => p (f.symm j) ≫ q j) := by
  apply native_hom_iff_cell rfl _ _ |>.2
  intro j
  let a := fun z => reindexSingleton e A.val z ≫ p z
  have h := standardPush_postequiv_collapse e f a q j
  let P := congrArg (fold 𝒮 Zₐ A.val) (fibreList_postequiv e f j)
  let Q := congrArg (fold 𝒮 Zₐ A.val) (equiv_fibreList e (f.symm j))
  let S := congrArg (fold 𝒮 Zₐ A.val) (equiv_fibreList (e.trans f) j)
  change standardPushSplit e f A.val j ≫
      (standardPushMap f a j ≫ (reindexSingleton f B.val j ≫ q j)) =
    𝟙 _ ≫ (reindexSingleton (e.trans f) A.val j ≫ p (f.symm j) ≫ q j)
  rw [h, Category.id_comp]
  unfold a reindexSingleton
  simp only [Category.assoc]
  change eqToHom P ≫ eqToHom Q ≫ (ρ_ (A.val (e.symm (f.symm j)))).hom ≫ p (f.symm j) ≫ q j =
    eqToHom S ≫ (ρ_ (A.val (e.symm (f.symm j)))).hom ≫ p (f.symm j) ≫ q j
  rw [eqToHom_trans_assoc]


set_option backward.isDefEq.respectTransparency false in
theorem nativeSingletonMap_congr {A D : Family C} (e f : Fin A.n ≃ Fin D.n)
    (p : ∀ j, A.val (e.symm j) ⟶ D.val j) (q : ∀ j, A.val (f.symm j) ⟶ D.val j)
    (h : ∀ i, e i = f i) (k : ∀ j, HEq (p j) (q j)) :
    nativeSingletonMap e p = nativeSingletonMap f q := by
  have he : e = f := Equiv.ext h
  subst f
  exact congrArg (nativeSingletonMap e) (funext fun j => eq_of_heq (k j))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
