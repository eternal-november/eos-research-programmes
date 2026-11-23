module
public import ContextualComposition.RelativeTensorBifunctor
public import ContextualComposition.RelativeTensorTranspose

@[expose] public section
namespace ContextualComposition.RelativeTensor.Parametric
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
variable {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G G' G'' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
set_option backward.isDefEq.respectTransparency false

def interchange (s : F ⟶ F') (t : G ⟶ G') : (mapFirst s ⋙ mapSecond t).toCatHom ≅ (mapSecond t ⋙ mapFirst s).toCatHom :=
  Cat.Hom.isoMk (eqToIso (factor_order s t))

@[simp] theorem interchange_app (s : F ⟶ F') (t : G ⟶ G') (x : Tensor F G) :
    (interchange s t).hom.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (factor_order s t)).app x = _
  rw [eqToHom_app]; rfl

def vary (t : G ⟶ G') : First.action.{v,u,vF,uF,vG,uG} G ⟶ First.action G' where
  app _ := (mapSecond t).toCatHom
  naturality s := interchange s t
  naturality_naturality := by
    intro A D f g m
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (mapSecond (F := D) t).map ((First.mapCell (G := G) m.as).app x) ≫ (interchange g t).hom.toNatTrans.app x =
      (interchange f t).hom.toNatTrans.app x ≫ (First.mapCell (G := G') m.as).app ((mapSecond (F := A) t).obj x)
    erw [interchange_app,interchange_app,Category.comp_id, Category.id_comp, First.cell_app, First.cell_app, Second.on_native,Functor.map_id]
    rfl
  naturality_id A := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (interchange (𝟙 A) t).hom.toNatTrans.app x ≫ (First.identityIso G' A).hom.toNatTrans.app ((mapSecond (F := A) t).obj x) =
      (mapSecond (F := A) t).map ((First.identityIso G A).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [interchange_app,First.identity_hom_app,Category.id_comp]
    rfl
  naturality_comp {A B D} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (interchange (f ≫ g) t).hom.toNatTrans.app x ≫ (First.compositeIso G' f g).hom.toNatTrans.app ((mapSecond (F := A) t).obj x) =
      (mapSecond (F := D) t).map ((First.compositeIso G f g).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
      (interchange g t).hom.toNatTrans.app ((mapFirst (G := G) f).obj x) ≫ 𝟙 _ ≫
      (mapFirst (G := G') g).map ((interchange f t).hom.toNatTrans.app x) ≫ 𝟙 _
    simp only [interchange_app,First.composite_hom_app,Functor.map_id]
    simp

def varyCell {s t : G ⟶ G'} (m : s ⟶ t) : vary.{v,u,vF,uF,vG,uG} s ⟶ vary t where
  as := {
    app _ := (Second.mapCell m.as).toCatHom₂
    naturality := by
      intro A D f
      apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
      change (Second.mapCell (F := D) m.as).app ((mapFirst (G := G) f).obj x) ≫ (interchange f t).hom.toNatTrans.app x =
        (interchange f s).hom.toNatTrans.app x ≫ (mapFirst (G := G') f).map ((Second.mapCell (F := A) m.as).app x)
      erw [interchange_app,interchange_app,Category.comp_id,Category.id_comp, Second.cell_app,Second.cell_app,First.on_native,Functor.map_id]
      rfl }

def varyId (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) : vary.{v,u,vF,uF,vG,uG} (𝟙 G) ≅ 𝟙 _ :=
  Pseudofunctor.StrongTrans.isoMk (fun F => Second.identityIso F G) (by
    intro A D s
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (Second.identityIso D G).hom.toNatTrans.app ((mapFirst s).obj x) ≫ (𝟙 _ ≫ 𝟙 _) =
      (interchange s (𝟙 G)).hom.toNatTrans.app x ≫ (mapFirst s).map ((Second.identityIso A G).hom.toNatTrans.app x)
    simp only [interchange_app,Second.identity_hom_app]
    simp
    exact ((mapFirst s).map_id x).symm)

def varyComp (s : G ⟶ G') (t : G' ⟶ G'') : vary.{v,u,vF,uF,vG,uG} (s ≫ t) ≅ vary s ≫ vary t :=
  Pseudofunctor.StrongTrans.isoMk (fun F => Second.compositeIso F s t) (by
    intro A D f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (Second.compositeIso D s t).hom.toNatTrans.app _ ≫ 𝟙 _ ≫ (mapSecond t).map ((interchange f s).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
        (interchange f t).hom.toNatTrans.app _ ≫ 𝟙 _ =
      (interchange f (s ≫ t)).hom.toNatTrans.app x ≫ (mapFirst f).map ((Second.compositeIso A s t).hom.toNatTrans.app x)
    simp only [Second.composite_hom_app,interchange_app]
    simp)

/-- The two-factor construction in curried form, for substitution of a tensor as another weak middle action. -/
def curried : Pseudofunctor (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) ((LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) ⥤ᵖ Cat) where
  obj := First.action
  map := vary
  map₂ := varyCell
  mapId := varyId
  mapComp := varyComp
  map₂_id _ := Pseudofunctor.StrongTrans.homCategory.ext fun F => (Second.action F).map₂_id _
  map₂_comp _ _ := Pseudofunctor.StrongTrans.homCategory.ext fun F => (Second.action F).map₂_comp _ _
  map₂_whisker_left := by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro F; exact (Second.action F).map₂_whisker_left ..
  map₂_whisker_right := by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro F; exact (Second.action F).map₂_whisker_right ..
  map₂_associator f g h := Pseudofunctor.StrongTrans.homCategory.ext fun F => (Second.action F).map₂_associator f g h
  map₂_left_unitor f := Pseudofunctor.StrongTrans.homCategory.ext fun F => (Second.action F).map₂_left_unitor f
  map₂_right_unitor f := Pseudofunctor.StrongTrans.homCategory.ext fun F => (Second.action F).map₂_right_unitor f

end ContextualComposition.RelativeTensor.Parametric
