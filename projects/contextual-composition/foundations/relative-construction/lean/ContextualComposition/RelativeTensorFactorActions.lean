module
public import ContextualComposition.RelativeTensorFactorComposition
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
set_option backward.isDefEq.respectTransparency false

namespace First
variable (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})

def identityIso (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) :
    (mapFirst (G := G) (𝟙 F)).toCatHom ≅ (𝟭 (Tensor F G)).toCatHom :=
  Cat.Hom.isoMk (eqToIso map_identity)

def compositeIso {F F' F'' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} (s : F ⟶ F') (t : F' ⟶ F'') :
    (mapFirst (G := G) (s ≫ t)).toCatHom ≅ (mapFirst s ⋙ mapFirst t).toCatHom :=
  Cat.Hom.isoMk (eqToIso (map_composite s t))

@[simp] theorem identity_hom_app (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (x : Tensor F G) :
    (identityIso G F).hom.toNatTrans.app x = 𝟙 x := by
  change (eqToHom (map_identity (F := F) (G := G))).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem composite_hom_app {F F' F'' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} (s : F ⟶ F') (t : F' ⟶ F'') (x : Tensor F G) :
    (compositeIso G s t).hom.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (map_composite (G := G) s t)).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem composite_inv_app {F F' F'' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} (s : F ⟶ F') (t : F' ⟶ F'') (x : Tensor F G) :
    (compositeIso G s t).inv.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (map_composite (G := G) s t).symm).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem cell_app {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {s t : F ⟶ F'} (m : s ⟶ t) (x : Tensor F G) :
    (mapCell m.as).app x = (insertion F' G x.as.mid).map (productMap ((m.as.app ⟨x.as.mid⟩).toNatTrans.app x.as.first) (𝟙 x.as.second)) := rfl

/-- Tensoring with a fixed contravariant factor acts on the bicategory of covariant actions, strong transformations, and modifications. -/
def action : Pseudofunctor (LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) Cat where
  obj F := Cat.of (Tensor F G)
  map s := (mapFirst s).toCatHom
  map₂ m := (mapCell m.as).toCatHom₂
  mapId := identityIso G
  mapComp := compositeIso G
  map₂_id s := congrArg NatTrans.toCatHom₂ ((homAction _ _ G).map_id s)
  map₂_comp m n := congrArg NatTrans.toCatHom₂ ((homAction _ _ G).map_comp m n)
  map₂_whisker_left := by
    intro A C D s t t' m
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, composite_hom_app, composite_inv_app, Cat.whiskerLeft_app,
      Category.id_comp]
    rfl
  map₂_whisker_right := by
    intro A C D s s' m t
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, composite_hom_app, composite_inv_app, Cat.whiskerRight_app,
      Category.id_comp]
    exact (on_native t ((m.as.app ⟨x.as.mid⟩).toNatTrans.app x.as.first) (𝟙 x.as.second)).symm
  map₂_associator := by
    intro A C D E s t r
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app, composite_hom_app, composite_inv_app, Functor.map_id,
      Category.id_comp]
    change (insertion E G x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map₂_left_unitor := by
    intro A D s
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, composite_hom_app, identity_hom_app, Category.id_comp]
    change (insertion D G x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map₂_right_unitor := by
    intro A D s
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, composite_hom_app, identity_hom_app, Category.id_comp]
    change (insertion D G x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _

end First

namespace Second
variable (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF})

def identityIso (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) :
    (mapSecond (F := F) (𝟙 G)).toCatHom ≅ (𝟭 (Tensor F G)).toCatHom :=
  Cat.Hom.isoMk (eqToIso map_identity)

def compositeIso {G G' G'' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}} (s : G ⟶ G') (t : G' ⟶ G'') :
    (mapSecond (F := F) (s ≫ t)).toCatHom ≅ (mapSecond s ⋙ mapSecond t).toCatHom :=
  Cat.Hom.isoMk (eqToIso (map_composite s t))

@[simp] theorem identity_hom_app (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) (x : Tensor F G) :
    (identityIso F G).hom.toNatTrans.app x = 𝟙 x := by
  change (eqToHom (map_identity (F := F) (G := G))).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem composite_hom_app {G G' G'' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}} (s : G ⟶ G') (t : G' ⟶ G'') (x : Tensor F G) :
    (compositeIso F s t).hom.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (map_composite (F := F) s t)).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem composite_inv_app {G G' G'' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}} (s : G ⟶ G') (t : G' ⟶ G'') (x : Tensor F G) :
    (compositeIso F s t).inv.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (map_composite (F := F) s t).symm).app x = _
  rw [eqToHom_app]
  rfl

@[simp] theorem cell_app {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}} {s t : G ⟶ G'} (m : s ⟶ t) (x : Tensor F G) :
    (mapCell m.as).app x = (insertion F G' x.as.mid).map (productMap (𝟙 x.as.first) ((m.as.app ⟨op x.as.mid⟩).toNatTrans.app x.as.second)) := rfl

/-- Tensoring with a fixed covariant factor acts on the bicategory of contravariant actions, strong transformations, and modifications. -/
def action : Pseudofunctor (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) Cat where
  obj G := Cat.of (Tensor F G)
  map s := (mapSecond s).toCatHom
  map₂ m := (mapCell m.as).toCatHom₂
  mapId := identityIso F
  mapComp := compositeIso F
  map₂_id s := congrArg NatTrans.toCatHom₂ ((homAction F _ _).map_id s)
  map₂_comp m n := congrArg NatTrans.toCatHom₂ ((homAction F _ _).map_comp m n)
  map₂_whisker_left := by
    intro A C D s t t' m
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, composite_hom_app, composite_inv_app, Cat.whiskerLeft_app,
      Category.id_comp]
    rfl
  map₂_whisker_right := by
    intro A C D s s' m t
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, composite_hom_app, composite_inv_app, Cat.whiskerRight_app,
      Category.id_comp]
    exact (on_native t (𝟙 x.as.first) ((m.as.app ⟨op x.as.mid⟩).toNatTrans.app x.as.second)).symm
  map₂_associator := by
    intro A C D E s t r
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app, composite_hom_app, composite_inv_app, Functor.map_id,
      Category.id_comp]
    change (insertion F E x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map₂_left_unitor := by
    intro A D s
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, composite_hom_app, identity_hom_app, Category.id_comp]
    change (insertion F D x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map₂_right_unitor := by
    intro A D s
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, composite_hom_app, identity_hom_app, Category.id_comp]
    change (insertion F D x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _

end Second
end ContextualComposition.RelativeTensor
