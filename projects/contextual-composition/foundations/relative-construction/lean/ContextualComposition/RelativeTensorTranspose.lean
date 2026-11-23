module
public import ContextualComposition.RelativeTensorMiddleAction

@[expose] public section
namespace ContextualComposition.RelativeTensor.Middle
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe w v u w' v' u' vCat uCat
variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
variable (M : A ⥤ᵖ (B ⥤ᵖ Cat.{vCat,uCat}))
set_option backward.isDefEq.respectTransparency false

def changeCell {a b : B} {f g : a ⟶ b} (n : f ⟶ g) : change M f ⟶ change M g where
  as := {
    app i := (M.obj i).map₂ n
    naturality := by
      intro i j t
      apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
      let p := (Cat.Hom.toNatIso ((M.map t).naturality f)).app x
      let q := (Cat.Hom.toNatIso ((M.map t).naturality g)).app x
      have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((M.map t).naturality_naturality n)) x
      change _ ≫ q.inv = p.inv ≫ _
      apply (cancel_epi p.hom).mp
      apply (cancel_mono q.hom).mp
      rw [p.hom_inv_id_assoc,← Category.assoc,Category.assoc,Category.assoc,q.inv_hom_id,Category.comp_id]
      exact h.symm }

private theorem unitOfIso {D : Type*} [Category* D] {x y z : D} (i : x ≅ y) (j : y ≅ z) (p : x ⟶ z)
    (h : i.hom = p ≫ j.inv) : j.hom ≫ (𝟙 _ ≫ 𝟙 _) = i.inv ≫ p := by
  apply (cancel_epi i.hom).mp
  simp only [Category.comp_id,Iso.hom_inv_id_assoc]
  rw [h,Category.assoc,Iso.inv_hom_id,Category.comp_id]

def changeUnit (b : B) : change M (𝟙 b) ≅ 𝟙 (atIndex M b) :=
  Pseudofunctor.StrongTrans.isoMk (fun i => (M.obj i).mapId b) (by
    intro i j t
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let p := (Cat.Hom.toNatIso ((M.map t).naturality (𝟙 b))).app x
    exact unitOfIso p ((Cat.Hom.toNatIso ((M.obj j).mapId b)).app _) _
      ((M.map t).naturality_id_hom_app b x))

def changeComposition {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    change M (f ≫ g) ≅ change M f ≫ change M g :=
  Pseudofunctor.StrongTrans.isoMk (fun i => (M.obj i).mapComp f g) (by
    intro i j t
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let n := (Cat.Hom.toNatIso ((M.obj i).mapComp f g)).app x
    let k := ((M.map t).app c).toFunctor
    have h := (M.map t).naturality_comp_inv_app f g x
    change _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ =
      ((M.map t).naturality (f ≫ g)).inv.toNatTrans.app x ≫ k.map n.hom
    erw [Category.id_comp,Category.id_comp,Category.comp_id,h]
    simp only [Category.assoc]
    erw [(k.mapIso n).inv_hom_id,Category.comp_id]
    rfl)

/-- Transpose a weak curried middle action. Its mixed comparison is the inverse of the given mixed square, and its two inner structural cells are the original component pseudofunctor's constraints. -/
def transpose : B ⥤ᵖ (A ⥤ᵖ Cat.{vCat,uCat}) where
  obj := atIndex M
  map := change M
  map₂ := changeCell M
  mapId := changeUnit M
  mapComp := changeComposition M
  map₂_id f := Pseudofunctor.StrongTrans.homCategory.ext fun i => (M.obj i).map₂_id f
  map₂_comp n k := Pseudofunctor.StrongTrans.homCategory.ext fun i => (M.obj i).map₂_comp n k
  map₂_whisker_left := by
    intro _ _ _ f _ _ n
    apply Pseudofunctor.StrongTrans.homCategory.ext; intro i
    exact (M.obj i).map₂_whisker_left f n
  map₂_whisker_right := by
    intro _ _ _ _ _ n g
    apply Pseudofunctor.StrongTrans.homCategory.ext; intro i
    exact (M.obj i).map₂_whisker_right n g
  map₂_associator f g h := Pseudofunctor.StrongTrans.homCategory.ext fun i => (M.obj i).map₂_associator f g h
  map₂_left_unitor f := Pseudofunctor.StrongTrans.homCategory.ext fun i => (M.obj i).map₂_left_unitor f
  map₂_right_unitor f := Pseudofunctor.StrongTrans.homCategory.ext fun i => (M.obj i).map₂_right_unitor f

end ContextualComposition.RelativeTensor.Middle
