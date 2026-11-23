module
public import ContextualComposition.RelativeTensorRightUnit
public import ContextualComposition.RelativeTensorTransformations

@[expose] public section
namespace ContextualComposition.RelativeTensor.RightUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF
variable {B : Type u} [Category.{v} B]
variable (a : B) (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF})
set_option backward.isDefEq.respectTransparency false

def identityLabel {i : B} (p : Discrete (i ⟶ a)) : p ≅ (backward (represented a) p.as).obj (Discrete.mk (𝟙 a)) :=
  eqToIso (Discrete.ext (Category.comp_id p.as).symm)

def component {i : B} (x : F.obj ⟨i⟩) (p : Discrete (i ⟶ a)) :
    (insertion F (represented a) i).obj (x,p) ≅ (sectionFunctor a F).obj ((forward F p.as).obj x) :=
  (insertion F (represented a) i).mapIso ((Iso.refl x).prod (identityLabel a p)) ≪≫
    balancing F (represented a) p.as x (Discrete.mk (𝟙 a))

private theorem commuteLabel {i : B} {p q : Discrete (i ⟶ a)} (l : p ⟶ q) {x y : F.obj ⟨i⟩} (f : x ⟶ y) :
    (insertion F (represented a) i).map (productMap f (𝟙 p)) ≫ (insertion F (represented a) i).map (productMap (𝟙 y) l) =
    (insertion F (represented a) i).map (productMap (𝟙 x) l) ≫ (insertion F (represented a) i).map (productMap f (𝟙 q)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (insertion F (represented a) i).map
  exact Prod.ext ((Category.comp_id f).trans (Category.id_comp f).symm) (Discrete.hom_eq (X := p) (Y := q))

theorem component_native {i : B} {p q : Discrete (i ⟶ a)} {x y : F.obj ⟨i⟩} (f : x ⟶ y) (l : p ⟶ q) :
    (insertion F (represented a) i).map (productMap f l) ≫ (component a F y q).hom =
      (component a F x p).hom ≫ (sectionFunctor a F).map ((evaluation a F).map ((insertion F (represented a) i).map (productMap f l))) := by
  obtain rfl : p = q := Discrete.ext (Discrete.eq_of_hom l)
  obtain rfl : l = 𝟙 p := Subsingleton.elim _ _
  rw [eval_native]
  erw [eqToHom_refl, Category.comp_id]
  let G := represented a
  have h := (restrict (𝟭 (Tensor F G))).natural p.as f (𝟙 (Discrete.mk (𝟙 a)))
  change (insertion F G i).map (productMap f ((backward G p.as).map (𝟙 (Discrete.mk (𝟙 a))))) ≫ _ =
    (balancing F G p.as x (Discrete.mk (𝟙 a))).hom ≫ (sectionFunctor a F).map ((forward F p.as).map f) at h
  rw [Functor.map_id] at h
  change _ ≫ (insertion F G i).map (productMap (𝟙 y) (identityLabel a p).hom) ≫ (balancing F G p.as y _).hom =
    ((insertion F G i).map (productMap (𝟙 x) (identityLabel a p).hom) ≫ _) ≫ _
  erw [← Category.assoc, commuteLabel a F, Category.assoc, h, Category.assoc]

private theorem labelComposite {i j : B} (u : i ⟶ j) (p : Discrete (j ⟶ a)) (x : F.obj ⟨i⟩) :
    (insertion F (represented a) i).map (productMap (𝟙 x) (identityLabel a ((backward (represented a) u).obj p)).hom) ≫
      (insertion F (represented a) i).map (productMap (𝟙 x) (((represented a).mapComp p.as.op.toLoc u.op.toLoc).hom.toNatTrans.app (Discrete.mk (𝟙 a)))) =
    (insertion F (represented a) i).map (productMap (𝟙 x) ((backward (represented a) u).map (identityLabel a p).hom)) := by
  rw [← Functor.map_comp]
  apply congrArg (insertion F (represented a) i).map
  exact Prod.ext (Category.id_comp _) (Discrete.hom_eq (α := i ⟶ a))

private theorem paste {D : Type*} [Category* D] {a b c d e f k : D}
    (z : a ⟶ b) (l : b ⟶ c) (last : c ⟶ d) (first : a ⟶ e) (n : e ⟶ f)
    (next : f ⟶ c) (w : e ⟶ k) (c₀ : a ⟶ f) (t : k ≅ d)
    (hc : w = n ≫ next ≫ last ≫ t.inv) (hn : c₀ ≫ next = z ≫ l) (hl : first ≫ n = c₀) :
    z ≫ l ≫ last = (first ≫ w) ≫ t.hom := by
  rw [hc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc first, hl, ← Category.assoc c₀, hn, Category.assoc]

theorem component_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (p : Discrete (j ⟶ a)) :
    (balancing F (represented a) u x p).hom ≫ (component a F ((forward F u).obj x) p).hom =
    (component a F x ((backward (represented a) u).obj p)).hom ≫
      (sectionFunctor a F).map ((evaluation a F).map (balancing F (represented a) u x p).hom) := by
  let G := represented a
  let t := (Cat.Hom.toNatIso (F.mapComp u.toLoc p.as.toLoc)).app x
  let S := restrict (𝟭 (Tensor F G))
  have hc := S.comp u p.as x (Discrete.mk (𝟙 a))
  have hn := S.natural u (𝟙 x) (identityLabel a p).hom
  change (insertion F G i).map (productMap (𝟙 x) ((backward G u).map (identityLabel a p).hom)) ≫ _ =
    _ ≫ (insertion F G j).map (productMap ((forward F u).map (𝟙 x)) (identityLabel a p).hom) at hn
  rw [Functor.map_id] at hn
  change (balancing F G (u ≫ p.as) x (Discrete.mk (𝟙 a))).hom =
    _ ≫ _ ≫ _ ≫ (sectionFunctor a F).map t.inv at hc
  rw [eval_balance]
  change _ ≫ (insertion F G j).map (productMap (𝟙 _) (identityLabel a p).hom) ≫ _ =
    (_ ≫ (balancing F G (u ≫ p.as) x (Discrete.mk (𝟙 a))).hom) ≫ (sectionFunctor a F).map t.hom
  exact paste _ _ _ _ _ _ _ _ ((sectionFunctor a F).mapIso t) hc hn (labelComposite a F u p x)

noncomputable def contraction : 𝟭 (Tensor F (represented a)) ≅ evaluation a F ⋙ sectionFunctor a F :=
  isoFromRestriction
    { components := fun _ => {
        app := fun x => (component a F x.1 x.2).hom
        naturality := fun _ _ f => component_native a F f.1 f.2 }
      square := fun u x y => component_balance a F u x y }
    (fun x => (component a F x.first x.second).isIso_hom)

/-- Right unit at the selected external endpoint for any weak covariant factor. -/
noncomputable def equivalence : Tensor F (represented a) ≌ F.obj ⟨a⟩ :=
  CategoryTheory.Equivalence.mk (evaluation a F) (sectionFunctor a F) (contraction a F) (sectionEvaluation a F)

end ContextualComposition.RelativeTensor.RightUnit
