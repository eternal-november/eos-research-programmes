module
public import ContextualComposition.RelativeTensorFactorActions

@[expose] public section
namespace ContextualComposition.RelativeTensor.Middle
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe w v u vCat uCat
variable {B : Type u} [Bicategory.{w,v} B]
set_option backward.isDefEq.respectTransparency false

/-- Evaluation at one index is a pseudofunctor on weak actions, strong transformations and arbitrary modifications. -/
def evaluate (b : B) : Pseudofunctor (B ⥤ᵖ Cat.{vCat,uCat}) Cat where
  obj P := P.obj b
  map s := s.app b
  map₂ n := n.as.app b
  map₂_id s := rfl
  map₂_comp m n := rfl
  mapId P := Iso.refl _
  mapComp s t := Iso.refl _
  map₂_whisker_left := by intros; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; rw [Category.comp_id, Category.id_comp]; rfl
  map₂_whisker_right := by intros; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; rw [Category.comp_id, Category.id_comp]; rfl
  map₂_associator := by intros; simp
  map₂_left_unitor := by intros; simp
  map₂_right_unitor := by intros; simp

section
variable {A : Type*} [Bicategory A] (M : A ⥤ᵖ (B ⥤ᵖ Cat.{vCat,uCat}))
abbrev atIndex (b : B) := M.comp (evaluate b)

private theorem flip {D : Type*} [Category* D] {a b c d : D} (i : a ≅ b) (j : c ≅ d) (f : a ⟶ c) (g : b ⟶ d)
    (h : f ≫ j.hom = i.hom ≫ g) : g ≫ j.inv = i.inv ≫ f := by
  apply (cancel_epi i.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem flip' {D : Type*} [Category* D] {a b c d : D} (i : a ≅ b) (j : c ≅ d) (f : a ⟶ c) (g : b ⟶ d)
    (h : f ≫ j.hom = i.hom ≫ g) : i.inv ≫ f = g ≫ j.inv := (flip i j f g h).symm

/-- Moving the inner index across a transition in the outer index uses the inverse of the supplied strong-naturality square. -/
def change {b c : B} (h : b ⟶ c) : atIndex M b ⟶ atIndex M c where
  app a := (M.obj a).map h
  naturality t := ((M.map t).naturality h).symm
  naturality_naturality n := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact flip ((Cat.Hom.toNatIso _).app x) ((Cat.Hom.toNatIso _).app x) _ _
      (NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((M.map₂ n).as.naturality h)) x)
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    have n := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((M.mapId a).hom.as.naturality h)) x
    let f := ((M.obj a).map h).toFunctor
    let i := (Cat.Hom.toNatIso ((M.map (𝟙 a)).naturality h)).app x
    let m := ((M.mapId a).hom.as.app b).toNatTrans.app x
    let v := ((M.mapId a).hom.as.app c).toNatTrans.app (f.obj x)
    change v ≫ (𝟙 _ ≫ 𝟙 _) = i.hom ≫ f.map m at n
    erw [Category.id_comp,Category.comp_id] at n
    change i.inv ≫ (v ≫ 𝟙 _) = f.map (m ≫ 𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    erw [Category.comp_id,Category.comp_id,Category.id_comp,Category.comp_id]
    rw [n, Iso.inv_hom_id_assoc]
  naturality_comp {a a' a''} s t := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let i := (Cat.Hom.toNatIso ((M.map (s ≫ t)).naturality h)).app x
    let p := ((M.obj a'').map h).toFunctor.map (((M.mapComp s t).hom.as.app b).toNatTrans.app x)
    let q := ((M.mapComp s t).hom.as.app c).toNatTrans.app (((M.obj a).map h).toFunctor.obj x)
    let j := (Cat.Hom.toNatIso ((M.map s ≫ M.map t).naturality h)).app x
    have n : q ≫ j.hom = i.hom ≫ p := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((M.mapComp s t).hom.as.naturality h)) x
    have hn := flip' i j q p n
    change i.inv ≫ (q ≫ 𝟙 _) = ((M.obj a'').map h).toFunctor.map (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.comp_id,Category.comp_id,Category.id_comp,Category.id_comp,Category.comp_id]
    change i.inv ≫ q = p ≫ _
    rw [hn]
    congr 1
    change (((𝟙 _ ≫ _) ≫ 𝟙 _) ≫ _) ≫ 𝟙 _ = _
    erw [Category.id_comp,Category.comp_id,Category.comp_id]
    rfl
end
end ContextualComposition.RelativeTensor.Middle
