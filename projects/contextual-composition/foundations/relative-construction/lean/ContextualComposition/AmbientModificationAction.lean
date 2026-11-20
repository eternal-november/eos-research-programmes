module
public import ContextualComposition.ContextadAmbientIsoMod
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientModificationAction
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue
open ContextadAmbientPayload CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{v} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}}
variable {a b c : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
variable (t : StrongTrans.Modification a b)
def coApp (x : Co Y) : (CoGrothendieck.map a).obj x ⟶ (CoGrothendieck.map b).obj x :=
  ⟨𝟙 x.base, (t.app ⟨op x.base⟩).toNatTrans.app x.fiber ≫
      (Z.toPseudofunctor'.mapId ⟨op x.base⟩).inv.toNatTrans.app _⟩
theorem modNat {x y : Co Y} (f : x ⟶ y) :
    (t.app ⟨op x.base⟩).toNatTrans.app ((Y.map f.base.op).toFunctor.obj y.fiber) ≫
      (b.naturality f.base.op.toLoc).hom.toNatTrans.app y.fiber =
    (a.naturality f.base.op.toLoc).hom.toNatTrans.app y.fiber ≫
      (Z.map f.base.op).toFunctor.map ((t.app ⟨op y.base⟩).toNatTrans.app y.fiber) :=
  congrArg (fun z => z.toNatTrans.app y.fiber) (t.naturality f.base.op.toLoc)
private theorem idMap {C : Type*} [Category* C] {J : C ⥤ C} (h : J = 𝟭 C)
    {x y : C} (f : x ⟶ y) (ex : x = J.obj x) (ey : J.obj y = y) :
    eqToHom ex ≫ J.map f ≫ eqToHom ey = f := by subst J; simp

private theorem coGrid {C : Type*} [Category* C] {J : C ⥤ C} (h : J = 𝟭 C)
    {x y z l m d : C} (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ d)
    (p : x ⟶ l) (q : l ⟶ m) (r : m ⟶ d) {k : C}
    (s : d = k) (t : l = J.obj l) (w : J.obj d = k)
    (H : a ≫ b ≫ c = p ≫ q ≫ r) :
    a ≫ b ≫ c ≫ eqToHom s = p ≫ eqToHom t ≫ J.map q ≫ J.map r ≫ eqToHom w := by
  subst J; subst k; simpa using H

theorem coNatural {x y : Co Y} (f : x ⟶ y) :
    (CoGrothendieck.map a).map f ≫ coApp t y = coApp t x ≫ (CoGrothendieck.map b).map f := by
  apply CoGrothendieck.Hom.ext _ _ (by change f.base ≫ 𝟙 _ = 𝟙 _ ≫ f.base; simp)
  simp only [coApp,CoGrothendieck.categoryStruct_comp_fiber,CoGrothendieck.map_map_fiber,Functor.toPseudofunctor'_mapId,Functor.toPseudofunctor'_mapComp,eqToIso.inv,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app,eqToHom_map,Category.assoc,eqToHom_trans,Functor.map_comp]
  let J := (Z.map (𝟙 (op x.base))).toFunctor
  have hJ : J = 𝟭 _ := congrArg Cat.Hom.toFunctor (Z.map_id _)
  let A := (a.app ⟨op x.base⟩).toFunctor
  let D := (b.app ⟨op x.base⟩).toFunctor
  let N := (t.app ⟨op x.base⟩).toNatTrans
  let v := (b.naturality f.base.op.toLoc).hom.toNatTrans.app y.fiber
  let u := (a.naturality f.base.op.toLoc).hom.toNatTrans.app y.fiber
  let w := (Z.map f.base.op).toFunctor.map ((t.app ⟨op y.base⟩).toNatTrans.app y.fiber)
  change A.map f.fiber ≫ u ≫ w ≫ eqToHom _ = N.app x.fiber ≫ eqToHom _ ≫ J.map (D.map f.fiber) ≫ J.map v ≫ eqToHom _
  apply coGrid hJ
  exact (congrArg (A.map f.fiber ≫ ·) (modNat t f).symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v) (N.naturality f.fiber)).trans (Category.assoc _ _ _)))
def coCell : CoGrothendieck.map a ⟶ CoGrothendieck.map b where
  app := coApp t
  naturality _ _ := coNatural t
def totalCell : totalStrong a ⟶ totalStrong b := whiskerLeft (read Y) (whiskerRight (coCell t) (write Z))
theorem totalVertical (x) : Pure ((proj Z).map ((totalCell t).app x)) := pureId _
end ContextualComposition.GrothendieckStep.AmbientModificationAction
