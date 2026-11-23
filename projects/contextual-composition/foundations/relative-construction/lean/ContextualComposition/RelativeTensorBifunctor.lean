module
public import ContextualComposition.RelativeTensorFactorActions
public import Mathlib.CategoryTheory.Bicategory.Product

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
set_option linter.checkUnivs false in
abbrev Factors (B : Type u) [Category.{v} B] := (LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) × (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Factors.{v,u,vF,uF,vG,uG} B}

def bothCell {f g : X ⟶ Y} (m : f ⟶ g) : mapBoth f.1 f.2 ⟶ mapBoth g.1 g.2 :=
  Functor.whiskerRight (First.mapCell m.1.as) (mapSecond f.2) ≫
    Functor.whiskerLeft (mapFirst g.1) (Second.mapCell m.2.as)

theorem bothCell_app {f g : X ⟶ Y} (m : f ⟶ g) (x : Tensor X.1 X.2) :
    (bothCell m).app x = (insertion Y.1 Y.2 x.as.mid).map
      (productMap ((m.1.as.app ⟨x.as.mid⟩).toNatTrans.app x.as.first) ((m.2.as.app ⟨op x.as.mid⟩).toNatTrans.app x.as.second)) := by
  change (mapSecond f.2).map ((insertion Y.1 X.2 x.as.mid).map (productMap _ (𝟙 x.as.second))) ≫
    (insertion Y.1 Y.2 x.as.mid).map (productMap (𝟙 _) _) = _
  erw [Second.on_native, Functor.map_id, ← (insertion Y.1 Y.2 x.as.mid).map_comp]
  apply congrArg (insertion Y.1 Y.2 x.as.mid).map
  exact Prod.ext (Category.comp_id _) (Category.id_comp _)

def bothHom (X Y : Factors.{v,u,vF,uF,vG,uG} B) : (X ⟶ Y) ⥤ (Tensor X.1 X.2 ⥤ Tensor Y.1 Y.2) where
  obj f := mapBoth f.1 f.2
  map := bothCell
  map_id f := by
    apply NatTrans.ext; funext x
    rw [bothCell_app]
    exact (insertion Y.1 Y.2 x.as.mid).map_id _
  map_comp m n := by
    apply NatTrans.ext; funext x
    rw [NatTrans.comp_app,bothCell_app,bothCell_app,bothCell_app,← Functor.map_comp]
    rfl

theorem both_identity (X : Factors.{v,u,vF,uF,vG,uG} B) : mapBoth (𝟙 X.1) (𝟙 X.2) = 𝟭 _ := by
  unfold mapBoth
  rw [First.map_identity,Second.map_identity,Functor.id_comp]

theorem both_composite (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapBoth (f.1 ≫ g.1) (f.2 ≫ g.2) = mapBoth f.1 f.2 ⋙ mapBoth g.1 g.2 := by
  unfold mapBoth
  rw [First.map_composite,Second.map_composite]
  have h := factor_order g.1 f.2
  change mapFirst g.1 ⋙ mapSecond f.2 = mapSecond f.2 ⋙ mapFirst g.1 at h
  exact congrArg (fun k => mapFirst f.1 ⋙ k ⋙ mapSecond g.2) h

def bothIdentityIso (X : Factors.{v,u,vF,uF,vG,uG} B) :
    (mapBoth (𝟙 X.1) (𝟙 X.2)).toCatHom ≅ (𝟭 (Tensor X.1 X.2)).toCatHom := Cat.Hom.isoMk (eqToIso (both_identity X))
def bothCompositeIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mapBoth (f.1 ≫ g.1) (f.2 ≫ g.2)).toCatHom ≅ (mapBoth f.1 f.2 ⋙ mapBoth g.1 g.2).toCatHom :=
  Cat.Hom.isoMk (eqToIso (both_composite f g))

@[simp] theorem both_identity_app (X : Factors.{v,u,vF,uF,vG,uG} B) (x : Tensor X.1 X.2) :
    (bothIdentityIso X).hom.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (both_identity X)).app x = _
  rw [eqToHom_app]; rfl
@[simp] theorem both_composite_app (f : X ⟶ Y) (g : Y ⟶ Z) (x : Tensor X.1 X.2) :
    (bothCompositeIso f g).hom.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (both_composite f g)).app x = _
  rw [eqToHom_app]; rfl
@[simp] theorem both_composite_inv_app (f : X ⟶ Y) (g : Y ⟶ Z) (x : Tensor X.1 X.2) :
    (bothCompositeIso f g).inv.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (both_composite f g).symm).app x = _
  rw [eqToHom_app]; rfl

/-- The actual path quotient and its simultaneous factor-change action form a pseudofunctor on the product of the two bicategories of actions. -/
def bifunctor : Pseudofunctor (Factors.{v,u,vF,uF,vG,uG} B) Cat where
  obj X := Cat.of (Tensor X.1 X.2)
  map f := (mapBoth f.1 f.2).toCatHom
  map₂ m := (bothCell m).toCatHom₂
  mapId := bothIdentityIso
  mapComp := bothCompositeIso
  map₂_id f := congrArg NatTrans.toCatHom₂ ((bothHom _ _).map_id f)
  map₂_comp m n := congrArg NatTrans.toCatHom₂ ((bothHom _ _).map_comp m n)
  map₂_whisker_left := by
    intro A C D f g h m
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, both_composite_app, both_composite_inv_app, Cat.whiskerLeft_app]
    change (bothCell (f ◁ m)).app x = 𝟙 _ ≫ (bothCell m).app ((mapBoth f.1 f.2).obj x) ≫ 𝟙 _
    erw [Category.id_comp]
    erw [Category.comp_id,bothCell_app,bothCell_app]
    rfl
  map₂_whisker_right := by
    intro A C D f g m h
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, both_composite_app, both_composite_inv_app, Cat.whiskerRight_app]
    change (bothCell (m ▷ h)).app x = 𝟙 _ ≫ (mapBoth h.1 h.2).map ((bothCell m).app x) ≫ 𝟙 _
    erw [Category.id_comp]
    erw [Category.comp_id,bothCell_app,bothCell_app,mapBoth_native]
    rfl
  map₂_associator := by
    intro A C D E f g h
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app, both_composite_app, both_composite_inv_app]
    change (bothCell (α_ f g h).hom).app x = _
    rw [bothCell_app]
    exact (insertion E.1 E.2 x.as.mid).map_id _
  map₂_left_unitor := by
    intro A D f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, both_composite_app, both_identity_app]
    change (bothCell (λ_ f).hom).app x = _
    rw [bothCell_app]
    exact (insertion D.1 D.2 x.as.mid).map_id _
  map₂_right_unitor := by
    intro A D f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, both_composite_app, both_identity_app]
    change (bothCell (ρ_ f).hom).app x = _
    rw [bothCell_app]
    exact (insertion D.1 D.2 x.as.mid).map_id _

end ContextualComposition.RelativeTensor
