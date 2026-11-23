module
public import ContextualComposition.RelativeTensorUniversal
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}}
variable {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}} {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false

namespace First
variable (s : Pseudofunctor.StrongTrans F F') (S : Cocone F' G D)
abbrev part (i : B) := (s.app ⟨i⟩).toFunctor
abbrev port {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) :=
  (Cat.Hom.toNatIso (s.naturality u.toLoc)).symm.app x

theorem port_unit {i : B} (x : F.obj ⟨i⟩) :
    (F'.mapId ⟨i⟩).inv.toNatTrans.app ((part s i).obj x) ≫ (port s (𝟙 i) x).hom =
      (part s i).map ((F.mapId ⟨i⟩).inv.toNatTrans.app x) := by
  have h := s.naturality_id_inv_app ⟨i⟩ x
  change _ ≫ (s.naturality (𝟙 _)).inv.toNatTrans.app x = _
  rw [h]
  exact (Cat.Hom.toNatIso (F'.mapId ⟨i⟩)).inv_hom_id_app_assoc _ _

theorem port_comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (x : F.obj ⟨i⟩) :
    (F'.mapComp u.toLoc v.toLoc).inv.toNatTrans.app ((part s i).obj x) ≫ (port s (u ≫ v) x).hom =
      (forward F' v).map (port s u x).hom ≫ (port s v ((forward F u).obj x)).hom ≫
      (part s k).map ((F.mapComp u.toLoc v.toLoc).inv.toNatTrans.app x) := by
  have h := s.naturality_comp_inv_app u.toLoc v.toLoc x
  change _ ≫ (s.naturality (u.toLoc ≫ v.toLoc)).inv.toNatTrans.app x = _
  rw [h]
  exact (Cat.Hom.toNatIso (F'.mapComp u.toLoc v.toLoc)).inv_hom_id_app_assoc _ _

def fiber (i : B) := ((part s i).prod (𝟭 _)) ⋙ S.fiber i
def balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :=
  S.bal u ((part s i).obj x) y ≪≫ (S.fiber j).mapIso ((port s u x).prod (Iso.refl y))

private theorem pair_nat {i j : B} (u : i ⟶ j) {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op j⟩} (p : x ⟶ x') (q : y ⟶ y') :
    (S.fiber j).map (productMap ((forward F' u).map ((part s i).map p)) q) ≫
      (S.fiber j).map (productMap (port s u x').hom (𝟙 y')) =
    (S.fiber j).map (productMap (port s u x).hom (𝟙 y)) ≫
      (S.fiber j).map (productMap ((part s j).map ((forward F u).map p)) q) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (S.fiber j).map
  exact Prod.ext ((s.naturality u.toLoc).inv.toNatTrans.naturality p) ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem pair_comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (x : F.obj ⟨i⟩) (y : G.obj ⟨op k⟩) :
    (S.fiber k).map (productMap ((F'.mapComp u.toLoc v.toLoc).inv.toNatTrans.app ((part s i).obj x)) (𝟙 y)) ≫
      (S.fiber k).map (productMap (port s (u ≫ v) x).hom (𝟙 y)) =
    (S.fiber k).map (productMap ((forward F' v).map (port s u x).hom) (𝟙 y)) ≫
      (S.fiber k).map (productMap (port s v ((forward F u).obj x)).hom (𝟙 y)) ≫
      (S.fiber k).map (productMap ((part s k).map ((F.mapComp u.toLoc v.toLoc).inv.toNatTrans.app x)) (𝟙 y)) := by
  simp only [← Functor.map_comp]
  apply congrArg (S.fiber k).map
  exact Prod.ext (port_comp s u v x) (congrArg (𝟙 y ≫ ·) (Category.id_comp _).symm)

/-- Pull a balanced cocone back along an arbitrary strong transformation on its covariant factor. -/
def pull : Cocone F G D where
  fiber := fiber s S
  bal := balance s S
  natural := by
    intro i j u x x' y y' p q
    change _ ≫ (S.bal u ((part s i).obj x') y').hom ≫ _ = ((S.bal u ((part s i).obj x) y).hom ≫ _) ≫ _
    erw [← Category.assoc, S.natural u ((part s i).map p) q, Category.assoc, pair_nat s S, Category.assoc]
    rfl
  unit {i} x y := by
    change (S.bal (𝟙 i) _ y).hom ≫ _ = _
    erw [S.unit, ← (S.fiber i).map_comp]
    apply congrArg (S.fiber i).map
    exact Prod.ext (port_unit s x) (Category.comp_id _)
  comp {i j k} u v x y := by
    have hn := S.natural v (port s u x).hom (𝟙 y)
    rw [Functor.map_id] at hn
    change (S.bal (u ≫ v) ((part s i).obj x) y).hom ≫ _ = _
    rw [S.comp]
    change (_ ≫ _ ≫ _ ≫ _) ≫ _ =
      (S.fiber i).map (productMap ((part s i).map (𝟙 x)) _) ≫ (_ ≫ _) ≫ (_ ≫ _) ≫ _
    rw [Functor.map_id]
    simp only [Category.assoc]
    erw [pair_comp s S u v x y, ← reassoc_of% hn]
    rfl

end First

/-- Action of a strong comparison of first factors on the actual relative tensor. -/
def mapFirst (s : Pseudofunctor.StrongTrans F F') : Tensor F G ⥤ Tensor F' G :=
  (First.pull s (restrict (𝟭 _))).extend

end ContextualComposition.RelativeTensor
