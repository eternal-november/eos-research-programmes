module
public import ContextualComposition.RelativeTensorFirstFactor
public import ContextualComposition.RelativeTensorSecondFactor
public import ContextualComposition.RelativeTensorTransformations
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
variable {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
set_option backward.isDefEq.respectTransparency false

namespace First
variable (s : Pseudofunctor.StrongTrans F F')
theorem on_native {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (p : x ⟶ x') (q : y ⟶ y') :
    (mapFirst s).map ((insertion F G i).map (productMap p q)) =
      (insertion F' G i).map (productMap ((part s i).map p) q) :=
  (pull s (restrict (𝟭 _))).extend_generator (Edge.native (F := F) (G := G) p q)

theorem on_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (mapFirst s).map (balancing F G u x y).hom =
      (balancing F' G u ((part s i).obj x) y).hom ≫ (insertion F' G j).map (productMap (port s u x).hom (𝟙 y)) :=
  (pull s (restrict (𝟭 _))).extend_generator (Edge.balance (F := F) (G := G) u x y)

variable {s} {t : Pseudofunctor.StrongTrans F F'} (m : Pseudofunctor.StrongTrans.Modification s t)

private theorem changePort {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) :
    (port s u x).hom ≫ (m.app ⟨j⟩).toNatTrans.app ((forward F u).obj x) =
      (forward F' u).map ((m.app ⟨i⟩).toNatTrans.app x) ≫ (port t u x).hom := by
  have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (m.naturality u.toLoc)) x
  apply (cancel_epi (port s u x).inv).mp
  apply (cancel_mono (port t u x).inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact h

def mapCell : mapFirst (G := G) s ⟶ mapFirst t :=
  fromRestriction {
    components := fun i => {
      app := fun x => (insertion F' G i).map (productMap ((m.app ⟨i⟩).toNatTrans.app x.1) (𝟙 x.2))
      naturality := by
        intro x y f
        change (mapFirst s).map ((insertion F G i).map (productMap f.1 f.2)) ≫ _ =
          _ ≫ (mapFirst t).map ((insertion F G i).map (productMap f.1 f.2))
        rw [on_native,on_native,← Functor.map_comp,← Functor.map_comp]
        apply congrArg (insertion F' G i).map
        exact Prod.ext ((m.app ⟨i⟩).toNatTrans.naturality f.1) ((Category.comp_id _).trans (Category.id_comp _).symm) }
    square := by
      intro i j u x y
      change (mapFirst s).map (balancing F G u x y).hom ≫ _ = _ ≫ (mapFirst t).map (balancing F G u x y).hom
      rw [on_balance,on_balance]
      have h := (restrict (𝟭 (Tensor F' G))).natural u ((m.app ⟨i⟩).toNatTrans.app x) (𝟙 y)
      change (insertion F' G i).map (productMap _ ((backward G u).map (𝟙 y))) ≫ _ = _ ≫ _ at h
      rw [Functor.map_id] at h
      erw [← Category.assoc _ (balancing F' G u ((part t i).obj x) y).hom, h, Category.assoc, Category.assoc]
      congr 1
      erw [← (insertion F' G j).map_comp, ← (insertion F' G j).map_comp]
      exact congrArg (insertion F' G j).map (Prod.ext (changePort m u x) rfl) }
end First

namespace Second
variable (s : Pseudofunctor.StrongTrans G G')
theorem on_native {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (p : x ⟶ x') (q : y ⟶ y') :
    (mapSecond s).map ((insertion F G i).map (productMap p q)) =
      (insertion F G' i).map (productMap p ((part s i).map q)) :=
  (pull s (restrict (𝟭 _))).extend_generator (Edge.native (F := F) (G := G) p q)

theorem on_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (mapSecond s).map (balancing F G u x y).hom =
      (insertion F G' i).map (productMap (𝟙 x) (port s u y).hom) ≫ (balancing F G' u x ((part s j).obj y)).hom :=
  (pull s (restrict (𝟭 _))).extend_generator (Edge.balance (F := F) (G := G) u x y)

variable {s} {t : Pseudofunctor.StrongTrans G G'} (m : Pseudofunctor.StrongTrans.Modification s t)

def mapCell : mapSecond (F := F) s ⟶ mapSecond t :=
  fromRestriction {
    components := fun i => {
      app := fun x => (insertion F G' i).map (productMap (𝟙 x.1) ((m.app ⟨op i⟩).toNatTrans.app x.2))
      naturality := by
        intro x y f
        change (mapSecond s).map ((insertion F G i).map (productMap f.1 f.2)) ≫ _ =
          _ ≫ (mapSecond t).map ((insertion F G i).map (productMap f.1 f.2))
        rw [on_native,on_native,← Functor.map_comp,← Functor.map_comp]
        apply congrArg (insertion F G' i).map
        exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) ((m.app ⟨op i⟩).toNatTrans.naturality f.2) }
    square := by
      intro i j u x y
      change (mapSecond s).map (balancing F G u x y).hom ≫ _ = _ ≫ (mapSecond t).map (balancing F G u x y).hom
      rw [on_balance,on_balance]
      have h := (restrict (𝟭 (Tensor F G'))).natural u (𝟙 x) ((m.app ⟨op j⟩).toNatTrans.app y)
      change _ ≫ _ = _ ≫ (insertion F G' j).map (productMap ((forward F u).map (𝟙 x)) _) at h
      rw [Functor.map_id] at h
      erw [Category.assoc, ← h, ← Category.assoc, ← Category.assoc]
      congr 1
      erw [← (insertion F G' i).map_comp, ← (insertion F G' i).map_comp]
      have v := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (m.naturality u.op.toLoc)) y
      exact congrArg (insertion F G' i).map (Prod.ext rfl v.symm) }
end Second

end ContextualComposition.RelativeTensor
