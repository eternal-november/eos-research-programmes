module
public import ContextualComposition.RelativeTensorUniversal
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false

namespace Second
variable (s : Pseudofunctor.StrongTrans G G') (S : Cocone F G' D)
abbrev part (i : B) := (s.app ⟨op i⟩).toFunctor
abbrev port {i j : B} (u : i ⟶ j) (y : G.obj ⟨op j⟩) := (Cat.Hom.toNatIso (s.naturality u.op.toLoc)).app y

theorem port_unit {i : B} (y : G.obj ⟨op i⟩) :
    (port s (𝟙 i) y).hom ≫ (G'.mapId ⟨op i⟩).hom.toNatTrans.app ((part s i).obj y) =
      (part s i).map ((G.mapId ⟨op i⟩).hom.toNatTrans.app y) := by
  have h := s.naturality_id_hom_app ⟨op i⟩ y
  change (s.naturality (𝟙 _)).hom.toNatTrans.app y ≫ _ = _
  rw [h, Category.assoc]
  erw [(Cat.Hom.toNatIso (G'.mapId ⟨op i⟩)).inv_hom_id_app, Category.comp_id]

theorem port_comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (y : G.obj ⟨op k⟩) :
    (port s (u ≫ v) y).hom ≫ (G'.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app ((part s k).obj y) =
      (part s i).map ((G.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app y) ≫
      (port s u ((backward G v).obj y)).hom ≫ (backward G' u).map (port s v y).hom := by
  have h := s.naturality_comp_hom_app v.op.toLoc u.op.toLoc y
  change (s.naturality (v.op.toLoc ≫ u.op.toLoc)).hom.toNatTrans.app y ≫ _ = _
  rw [h]
  simp only [Category.assoc]
  erw [(Cat.Hom.toNatIso (G'.mapComp v.op.toLoc u.op.toLoc)).inv_hom_id_app, Category.comp_id]
  rfl

def fiber (i : B) := ((𝟭 _).prod (part s i)) ⋙ S.fiber i
def balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :=
  (S.fiber i).mapIso ((Iso.refl x).prod (port s u y)) ≪≫ S.bal u x ((part s j).obj y)

private theorem pair_nat {i j : B} (u : i ⟶ j) {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op j⟩} (p : x ⟶ x') (q : y ⟶ y') :
    (S.fiber i).map (productMap p ((part s i).map ((backward G u).map q))) ≫
      (S.fiber i).map (productMap (𝟙 x') (port s u y').hom) =
    (S.fiber i).map (productMap (𝟙 x) (port s u y).hom) ≫
      (S.fiber i).map (productMap p ((backward G' u).map ((part s j).map q))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (S.fiber i).map
  exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) ((s.naturality u.op.toLoc).hom.toNatTrans.naturality q)

private theorem pair_comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (x : F.obj ⟨i⟩) (y : G.obj ⟨op k⟩) :
    (S.fiber i).map (productMap (𝟙 x) (port s (u ≫ v) y).hom) ≫
      (S.fiber i).map (productMap (𝟙 x) ((G'.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app ((part s k).obj y))) =
    (S.fiber i).map (productMap (𝟙 x) ((part s i).map ((G.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app y))) ≫
      (S.fiber i).map (productMap (𝟙 x) (port s u ((backward G v).obj y)).hom) ≫
      (S.fiber i).map (productMap (𝟙 x) ((backward G' u).map (port s v y).hom)) := by
  simp only [← Functor.map_comp]
  apply congrArg (S.fiber i).map
  exact Prod.ext (congrArg (𝟙 x ≫ ·) (Category.id_comp _).symm) (port_comp s u v y)

def pull : Cocone F G D where
  fiber := fiber s S
  bal := balance s S
  natural := by
    intro i j u x x' y y' p q
    change _ ≫ (S.fiber i).map (productMap (𝟙 x') (port s u y').hom) ≫ _ = (_ ≫ _) ≫ _
    erw [← Category.assoc, pair_nat s S, Category.assoc, S.natural u p ((part s j).map q), Category.assoc]
    rfl
  unit {i} x y := by
    change _ ≫ (S.bal (𝟙 i) x _).hom = _
    erw [S.unit, ← (S.fiber i).map_comp]
    apply congrArg (S.fiber i).map
    exact Prod.ext (Category.id_comp _) (port_unit s y)
  comp {i j k} u v x y := by
    have hn := S.natural u (𝟙 x) (port s v y).hom
    rw [Functor.map_id] at hn
    change (S.fiber i).map (productMap (𝟙 x) (port s (u ≫ v) y).hom) ≫ (S.bal (u ≫ v) x ((part s k).obj y)).hom = _
    rw [S.comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ _ =
      _ ≫ (_ ≫ _) ≫ (_ ≫ _) ≫ (S.fiber k).map (productMap _ ((part s k).map (𝟙 y)))
    rw [Functor.map_id]
    simp only [Category.assoc]
    erw [← Category.assoc ((S.fiber i).map (productMap (𝟙 x) (port s (u ≫ v) y).hom)), pair_comp s S u v x y]
    simp only [Category.assoc]
    erw [reassoc_of% hn]
    rfl

end Second

def mapSecond (s : Pseudofunctor.StrongTrans G G') : Tensor F G ⥤ Tensor F G' :=
  (Second.pull s (restrict (𝟭 _))).extend

end ContextualComposition.RelativeTensor
