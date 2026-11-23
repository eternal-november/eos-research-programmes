module
public import ContextualComposition.IndexedEndpointAction

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Indexed
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

section Reindex
variable {A B D : Type*} [Bicategory A] [Bicategory B] [Bicategory D]
variable (H : A ⥤ᵖ B) {F G : B ⥤ᵖ D}

/-- Precompose a strong transformation by a pseudofunctor, retaining its actual component at every reindexed object. -/
def reindex (η : F ⟶ G) : H.comp F ⟶ H.comp G where
  app x := η.app (H.obj x)
  naturality f := η.naturality (H.map f)
  naturality_naturality α := η.naturality_naturality (H.map₂ α)
  naturality_id x := by
    change (η.naturality (H.map (𝟙 x))).hom ≫ η.app _ ◁ (G.map₂ (H.mapId x).hom ≫ (G.mapId _).hom) =
      (F.map₂ (H.mapId x).hom ≫ (F.mapId _).hom) ▷ η.app _ ≫ _ ≫ _
    rw [whiskerLeft_comp,comp_whiskerRight,Category.assoc,← η.naturality_naturality_assoc (H.mapId x).hom,η.naturality_id]
  naturality_comp f g := by
    change (η.naturality (H.map (f ≫ g))).hom ≫ η.app _ ◁ (G.map₂ (H.mapComp f g).hom ≫ (G.mapComp _ _).hom) =
      (F.map₂ (H.mapComp f g).hom ≫ (F.mapComp _ _).hom) ▷ η.app _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _
    rw [whiskerLeft_comp,comp_whiskerRight,Category.assoc,← η.naturality_naturality_assoc (H.mapComp f g).hom,η.naturality_comp]
    rfl

def reindexCell {η θ : F ⟶ G} (m : η ⟶ θ) : reindex H η ⟶ reindex H θ :=
  ⟨⟨fun x => m.as.app (H.obj x),fun f => m.as.naturality (H.map f)⟩⟩

def reindexIso {η θ : F ⟶ G} (m : η ≅ θ) : reindex H η ≅ reindex H θ where
  hom := reindexCell H m.hom
  inv := reindexCell H m.inv
  hom_inv_id := Pseudofunctor.StrongTrans.homCategory.ext fun x =>
    congrArg (fun k => k.as.app (H.obj x)) m.hom_inv_id
  inv_hom_id := Pseudofunctor.StrongTrans.homCategory.ext fun x =>
    congrArg (fun k => k.as.app (H.obj x)) m.inv_hom_id

def reindexEquivalence (E : Bicategory.Equivalence F G) : Bicategory.Equivalence (H.comp F) (H.comp G) where
  hom := reindex H E.hom
  inv := reindex H E.inv
  unit := reindexIso H E.unit
  counit := reindexIso H E.counit
  left_triangle := by
    apply Iso.ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro x
    exact congrArg (fun k => k.hom.as.app (H.obj x)) E.left_triangle
end Reindex

universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable (K : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vK,uK}) (L : LocallyDiscrete C ⥤ᵖ Cat.{vL,uL})
variable (e : Pseudofunctor.CoGrothendieck K ⥤ C) (d : Pseudofunctor.Grothendieck L ⥤ C)

/-- Normalization at the actual pair of context and content endpoints is an adjoint equivalence of indexed Cat-valued pseudofunctors. -/
noncomputable def normalizationEquivalence :
    Bicategory.Equivalence ((action K L e d).comp (Presentation.largeLocalization C))
      ((action K L e d).comp (Presentation.largeComma C)) :=
  reindexEquivalence (action K L e d) (Presentation.normalizationEquivalence C)

theorem comma_body {i j : Cᵒᵖ × C} (p : i ⟶ j)
    (s : Comma (presentation K L e d i).source (presentation K L e d i).target) :
    ((commaFunctor (transport K L e d p)).obj s).hom =
      e.map (Pseudofunctor.CoGrothendieck.cartesianLift s.left p.1.unop) ≫ s.hom ≫
        d.map ((outputLift L p.2).app s.right) := rfl

theorem comma_grades {i j : Cᵒᵖ × C} (p : i ⟶ j)
    {s t : Comma (presentation K L e d i).source (presentation K L e d i).target} (a : s ⟶ t) :
    ((commaFunctor (transport K L e d p)).map a).left = (K.map p.1.toLoc).toFunctor.map a.left ∧
      ((commaFunctor (transport K L e d p)).map a).right = (L.map p.2.toLoc).toFunctor.map a.right := ⟨rfl,rfl⟩

end ContextualComposition.Factorization.Endpoint.Indexed
