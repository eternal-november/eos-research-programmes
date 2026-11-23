module
public import ContextualComposition.EmptyContentTransport
public import Mathlib.CategoryTheory.Functor.Currying

/-! A fibrewise choice of inverse to transport from the empty interface induces a total equivalence over the same base. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyContentTransport
open CategoryTheory CategoryTheory.Bicategory ContextualComposition.Factorization.Endpoint.Indexed
set_option backward.isDefEq.respectTransparency false
universe u w v
variable (L : LocallyDiscrete (Type u) ⥤ᵖ Cat.{v,w}) (h : ∀ B, (E L B).IsEquivalence)

def comparisonFF : (constantize L).FullyFaithful :=
  fullyFaithful L (fun B => by let := h B; exact (E L B).asEquivalence.fullyFaithfulFunctor)

def backObj (X : Total L) : Base L := by
  let := h X.base
  exact ⟨X.base,(E L X.base).asEquivalence.inverse.obj X.fiber⟩

def verticalIso (X : Total L) : (constantize L).obj (backObj L h X) ≅ X := by
  let := h X.base
  exact (outInclusion L X.base).mapIso ((E L X.base).asEquivalence.counitIso.app X.fiber)

def inverse : Total L ⥤ Base L where
  obj := backObj L h
  map {X Y} f := (comparisonFF L h).preimage ((verticalIso L h X).hom ≫ f ≫ (verticalIso L h Y).inv)
  map_id X := by apply (comparisonFF L h).map_injective; simp
  map_comp {X Y Z} f g := by
    apply (comparisonFF L h).map_injective
    rw [Functor.map_comp]
    simp only [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_assoc]

def counit : inverse L h ⋙ constantize L ≅ 𝟭 _ :=
  NatIso.ofComponents (verticalIso L h) (by
    intro X Y f
    change (constantize L).map ((comparisonFF L h).preimage _) ≫ _ = _
    simp)

def unit : 𝟭 _ ≅ constantize L ⋙ inverse L h :=
  NatIso.ofComponents (fun X => ((comparisonFF L h).preimageIso (verticalIso L h ((constantize L).obj X))).symm)
    (by
      intro X Y f
      apply (comparisonFF L h).map_injective
      rw [Functor.map_comp, Functor.map_comp]
      change (constantize L).map f ≫ (constantize L).map ((comparisonFF L h).preimage _) =
        (constantize L).map ((comparisonFF L h).preimage _) ≫ (constantize L).map ((comparisonFF L h).preimage _)
      simp only [Functor.FullyFaithful.map_preimage, Iso.inv_hom_id_assoc])

def equivalence : Base L ≌ Total L where
  functor := constantize L
  inverse := inverse L h
  unitIso := unit L h
  counitIso := counit L h
  functor_unitIso_comp X := by simp [unit,counit]

theorem inverse_over_base : inverse L h ⋙ CategoryTheory.Prod.fst _ _ = Pseudofunctor.Grothendieck.forget L := by
  apply Functor.ext (fun _ => rfl)

theorem counit_over (X : Total L) : ((counit L h).hom.app X).base = 𝟙 X.base := rfl
theorem unit_over (X : Base L) : ((unit L h).hom.app X).1 = 𝟙 X.1 := rfl

/-- Constantized grades give honest Set endofunctors on extensions. A native grade arrow induces a natural transformation. -/
def extensions (d : Total L ⥤ Type u) : Fibre L Zero ⥤ (Type u ⥤ Type u) :=
  (Functor.curry.obj ((CategoryTheory.Prod.swap _ _) ⋙ constantize L ⋙ d))

end ContextualComposition.EmptyContentTransport
