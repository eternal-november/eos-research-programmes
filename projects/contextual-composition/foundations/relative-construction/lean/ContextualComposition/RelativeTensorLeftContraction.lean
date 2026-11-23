module
public import ContextualComposition.RelativeTensorLeftUnit
public import ContextualComposition.RelativeTensorTransformations

@[expose] public section
namespace ContextualComposition.RelativeTensor.LeftUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vG uG
variable {B : Type u} [Category.{v} B]
variable (a : B) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})
set_option backward.isDefEq.respectTransparency false

def identityLabel {i : B} (x : Discrete (a ⟶ i)) : (forward (represented a) x.as).obj (Discrete.mk (𝟙 a)) ≅ x :=
  eqToIso (Discrete.ext (Category.id_comp x.as))

def component {i : B} (x : Discrete (a ⟶ i)) (y : G.obj ⟨op i⟩) :
    (sectionFunctor a G).obj ((backward G x.as).obj y) ≅ (insertion (represented a) G i).obj (x,y) :=
  balancing (represented a) G x.as (Discrete.mk (𝟙 a)) y ≪≫
    (insertion (represented a) G i).mapIso ((identityLabel a x).prod (Iso.refl y))

private theorem commuteLabel {i : B} {p q : Discrete (a ⟶ i)} (l : p ⟶ q) {x y : G.obj ⟨op i⟩} (f : x ⟶ y) :
    (insertion (represented a) G i).map (productMap (𝟙 p) f) ≫ (insertion (represented a) G i).map (productMap l (𝟙 y)) =
    (insertion (represented a) G i).map (productMap l (𝟙 x)) ≫ (insertion (represented a) G i).map (productMap (𝟙 q) f) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (insertion (represented a) G i).map
  apply Prod.ext
  · exact Discrete.hom_eq (X := p) (Y := q)
  · exact (Category.comp_id f).trans (Category.id_comp f).symm

theorem component_native {i : B} {p q : Discrete (a ⟶ i)} {x y : G.obj ⟨op i⟩} (l : p ⟶ q) (f : x ⟶ y) :
    (sectionFunctor a G).map ((evaluation a G).map ((insertion (represented a) G i).map (productMap l f))) ≫ (component a G q y).hom =
      (component a G p x).hom ≫ (insertion (represented a) G i).map (productMap l f) := by
  obtain rfl : p = q := Discrete.ext (Discrete.eq_of_hom l)
  obtain rfl : l = 𝟙 p := Subsingleton.elim _ _
  rw [eval_native]
  erw [eqToHom_refl, Category.comp_id]
  let F := represented a
  have h := (restrict (𝟭 (Tensor F G))).natural p.as (𝟙 (Discrete.mk (𝟙 a))) f
  change (sectionFunctor a G).map ((backward G p.as).map f) ≫ (balancing F G p.as (Discrete.mk (𝟙 a)) y).hom =
    (balancing F G p.as (Discrete.mk (𝟙 a)) x).hom ≫
      (insertion F G i).map (productMap ((forward F p.as).map (𝟙 (Discrete.mk (𝟙 a)))) f) at h
  rw [Functor.map_id] at h
  change _ ≫ (balancing F G p.as _ y).hom ≫ (insertion F G i).map (productMap (identityLabel a p).hom (𝟙 y)) =
    ((balancing F G p.as _ x).hom ≫ (insertion F G i).map (productMap (identityLabel a p).hom (𝟙 x))) ≫ _
  erw [← Category.assoc, h, Category.assoc, commuteLabel a G, Category.assoc]

private theorem labelComposite {i j : B} (p : Discrete (a ⟶ i)) (u : i ⟶ j) (y : G.obj ⟨op j⟩) :
    (insertion (represented a) G j).map (productMap (((represented a).mapComp p.as.toLoc u.toLoc).inv.toNatTrans.app (Discrete.mk (𝟙 a))) (𝟙 y)) ≫
      (insertion (represented a) G j).map (productMap (identityLabel a ((forward (represented a) u).obj p)).hom (𝟙 y)) =
    (insertion (represented a) G j).map (productMap ((forward (represented a) u).map (identityLabel a p).hom) (𝟙 y)) := by
  rw [← Functor.map_comp]
  apply congrArg (insertion (represented a) G j).map
  exact Prod.ext (Discrete.hom_eq (α := a ⟶ j)) (Category.id_comp _)

theorem component_balance {i j : B} (u : i ⟶ j) (p : Discrete (a ⟶ i)) (y : G.obj ⟨op j⟩) :
    (sectionFunctor a G).map ((evaluation a G).map (balancing (represented a) G u p y).hom) ≫
      (component a G ((forward (represented a) u).obj p) y).hom =
    (component a G p ((backward G u).obj y)).hom ≫ (balancing (represented a) G u p y).hom := by
  let F := represented a
  let t := (Cat.Hom.toNatIso (G.mapComp u.op.toLoc p.as.op.toLoc)).app y
  let S := restrict (𝟭 (Tensor F G))
  have hc := S.comp p.as u (Discrete.mk (𝟙 a)) y
  have hn := S.natural u (identityLabel a p).hom (𝟙 y)
  change (insertion F G i).map (productMap (identityLabel a p).hom ((backward G u).map (𝟙 y))) ≫ _ =
    _ ≫ (insertion F G j).map (productMap ((forward F u).map (identityLabel a p).hom) (𝟙 y)) at hn
  rw [Functor.map_id] at hn
  change (balancing F G (p.as ≫ u) (Discrete.mk (𝟙 a)) y).hom =
    (sectionFunctor a G).map t.hom ≫ _ ≫ _ ≫ _ at hc
  rw [eval_balance]
  change (sectionFunctor a G).map t.inv ≫ (balancing F G (p.as ≫ u) (Discrete.mk (𝟙 a)) y).hom ≫ _ =
    ((balancing F G p.as (Discrete.mk (𝟙 a)) _).hom ≫ _) ≫ _
  erw [hc]
  simp only [Category.assoc]
  erw [((sectionFunctor a G).mapIso t).inv_hom_id_assoc, labelComposite a G p u y, hn]
  rfl

noncomputable def contraction : evaluation a G ⋙ sectionFunctor a G ≅ 𝟭 (Tensor (represented a) G) :=
  isoFromRestriction
    { components := fun _ => {
        app := fun x => (component a G x.1 x.2).hom
        naturality := fun _ _ f => component_native a G f.1 f.2 }
      square := fun u x y => component_balance a G u x y }
    (fun x => (component a G x.first x.second).isIso_hom)

/-- Left unit of the relative tensor at one external endpoint, for arbitrary weak action of the other factor. -/
noncomputable def equivalence : Tensor (represented a) G ≌ G.obj ⟨op a⟩ :=
  CategoryTheory.Equivalence.mk (evaluation a G) (sectionFunctor a G) (contraction a G).symm (sectionEvaluation a G)

end ContextualComposition.RelativeTensor.LeftUnit
