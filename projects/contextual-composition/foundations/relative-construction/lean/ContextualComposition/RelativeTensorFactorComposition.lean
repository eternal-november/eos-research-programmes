module
public import ContextualComposition.RelativeTensorInterchange
public import ContextualComposition.RelativeTensorGeneratorComparison

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
variable {F F' F'' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G G' G'' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
set_option backward.isDefEq.respectTransparency false

private theorem pad {D : Type*} [Category* D] {x y : D} {p q : x ⟶ y} (h : p = q) : p ≫ 𝟙 _ = 𝟙 _ ≫ q := by simpa using h

namespace First
theorem port_identity {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) : (port (𝟙 F) u x).hom = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

theorem port_composite (s : F ⟶ F') (t : F' ⟶ F'') {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) :
    (port (s ≫ t) u x).hom = (port t u ((part s i).obj x)).hom ≫ (part t j).map (port s u x).hom := by
  change (((𝟙 _ ≫ _) ≫ 𝟙 _) ≫ _) ≫ 𝟙 _ = _
  erw [Category.id_comp,Category.comp_id,Category.comp_id]
  rfl

theorem map_identity : mapFirst (G := G) (𝟙 F) = 𝟭 _ := by
  fapply extGenerators
  · intro x; rfl
  · intro i x x' y y' f g
    apply pad
    rw [on_native]
    rfl
  · intro i j u x y
    apply pad
    rw [on_balance,port_identity]
    change _ ≫ (insertion F G j).map (𝟙 _) = _
    rw [Functor.map_id,Category.comp_id]
    rfl

theorem map_composite (s : F ⟶ F') (t : F' ⟶ F'') : mapFirst (G := G) (s ≫ t) = mapFirst s ⋙ mapFirst t := by
  fapply extGenerators
  · intro x; rfl
  · intro i x x' y y' f g
    apply pad
    dsimp only [Functor.comp_map]
    rw [on_native,on_native,on_native]
    rfl
  · intro i j u x y
    apply pad
    dsimp only [Functor.comp_map]
    rw [on_balance,on_balance,Functor.map_comp,on_balance,on_native, Category.assoc, port_composite]
    congr 1
    erw [← (insertion F'' G j).map_comp]
    apply congrArg (insertion F'' G j).map
    exact Prod.ext rfl (Category.id_comp _).symm

def homAction (F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) :
    (F ⟶ F') ⥤ (Tensor F G ⥤ Tensor F' G) where
  obj := mapFirst
  map m := mapCell m.as
  map_id s := by
    apply NatTrans.ext; funext x
    change (insertion F' G x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map_comp m n := by
    apply NatTrans.ext; funext x
    change (insertion F' G x.as.mid).map (productMap (_ ≫ _) (𝟙 x.as.second)) = _ ≫ _
    erw [← (insertion F' G x.as.mid).map_comp]
    apply congrArg (insertion F' G x.as.mid).map
    exact Prod.ext rfl (Category.id_comp _).symm
end First

namespace Second
theorem port_identity {i j : B} (u : i ⟶ j) (y : G.obj ⟨op j⟩) : (port (𝟙 G) u y).hom = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

theorem port_composite (s : G ⟶ G') (t : G' ⟶ G'') {i j : B} (u : i ⟶ j) (y : G.obj ⟨op j⟩) :
    (port (s ≫ t) u y).hom = (part t i).map (port s u y).hom ≫ (port t u ((part s j).obj y)).hom := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  erw [Category.id_comp,Category.id_comp,Category.comp_id]
  rfl

theorem map_identity : mapSecond (F := F) (𝟙 G) = 𝟭 _ := by
  fapply extGenerators
  · intro x; rfl
  · intro i x x' y y' f g
    apply pad
    rw [on_native]
    rfl
  · intro i j u x y
    apply pad
    rw [on_balance,port_identity]
    change (insertion F G i).map (𝟙 _) ≫ _ = _
    rw [Functor.map_id,Category.id_comp]
    rfl

theorem map_composite (s : G ⟶ G') (t : G' ⟶ G'') : mapSecond (F := F) (s ≫ t) = mapSecond s ⋙ mapSecond t := by
  fapply extGenerators
  · intro x; rfl
  · intro i x x' y y' f g
    apply pad
    dsimp only [Functor.comp_map]
    rw [on_native,on_native,on_native]
    rfl
  · intro i j u x y
    apply pad
    dsimp only [Functor.comp_map]
    rw [on_balance,on_balance,Functor.map_comp,on_native,on_balance, ← Category.assoc, port_composite]
    congr 1
    erw [← (insertion F G'' i).map_comp]
    apply congrArg (insertion F G'' i).map
    exact Prod.ext (Category.id_comp _).symm rfl

def homAction (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) :
    (G ⟶ G') ⥤ (Tensor F G ⥤ Tensor F G') where
  obj := mapSecond
  map m := mapCell m.as
  map_id s := by
    apply NatTrans.ext; funext x
    change (insertion F G' x.as.mid).map (𝟙 _) = 𝟙 _
    exact Functor.map_id _ _
  map_comp m n := by
    apply NatTrans.ext; funext x
    change (insertion F G' x.as.mid).map (productMap (𝟙 x.as.first) (_ ≫ _)) = _ ≫ _
    erw [← (insertion F G' x.as.mid).map_comp]
    apply congrArg (insertion F G' x.as.mid).map
    exact Prod.ext (Category.id_comp _).symm rfl
end Second

end ContextualComposition.RelativeTensor
