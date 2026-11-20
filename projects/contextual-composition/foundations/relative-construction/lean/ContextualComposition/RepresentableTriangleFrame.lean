module
public import ContextualComposition.RepresentableTriangleInterchange
public import ContextualComposition.RepresentableFoldLeftUnit
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableTriangleFrame
open CategoryTheory CategoryTheory.Bicategory
open AmbientHorizontalDiagrams AmbientHorizontalNaturality
open RepresentableKleisliConstraints RepresentableFoldLeftUnit RepresentableTriangleInterchange
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
section Generic
variable {C : Type*} [Bicategory C] [Bicategory.Strict C] (F : StrictPseudofunctor C C)
variable {A B D : C} (f : A ⟶ F.obj B) (g : B ⟶ F.obj D)
variable (e : B ⟶ F.obj B) (h : F.obj D ⟶ F.obj (F.obj D))
variable (m : F.obj (F.obj B) ⟶ F.obj B) (n : F.obj (F.obj (F.obj D)) ⟶ F.obj (F.obj D))
variable (q : F.obj (F.obj D) ⟶ F.obj D)
variable (s : g ≫ h ≅ e ≫ F.map g) (t : F.map (F.map g) ≫ n ≅ m ≫ F.map g)
variable (a : n ≫ q ≅ F.map q ≫ q) (l : h ≫ q ≅ 𝟙 _) (r : F.map e ≫ m ≅ 𝟙 _)
def expand {x y z w : C} (p : x ⟶ y) (t : y ⟶ z) (q : z ⟶ w) :
    F.map ((p ≫ t) ≫ q) ≅ (F.map p ≫ F.map t) ≫ F.map q :=
  F.mapComp (p ≫ t) q ≪≫ whiskerRightIso (F.mapComp p t) (F.map q)
def front {x y z w v : C} (f : x ⟶ y) (p : y ⟶ z) (m : z ⟶ y) (g : y ⟶ w) (q : w ⟶ v) :
    (((f ≫ p) ≫ m) ≫ g) ≫ q ≅ f ≫ (((p ≫ m) ≫ g) ≫ q) :=
  whiskerRightIso (whiskerRightIso (α_ f p m) g) q ≪≫ whiskerRightIso (α_ f (p ≫ m) g) q ≪≫ (α_ f ((p ≫ m) ≫ g) q)
def startLong :=
  moveTail (f ≫ F.map e) q t.symm ≪≫
    whiskerLeftIso ((f ≫ F.map e) ≫ F.map (F.map g)) a ≪≫
    moveHead f (F.map e) (F.map (F.map g)) (F.map q) q ≪≫
    whiskerRightIso (whiskerLeftIso f (expand F e (F.map g) q).symm) q
def longer :=
  startLong F f g e m n q t a ≪≫ whiskerRightIso (whiskerLeftIso f (F.map₂Iso (bare (f := g) (p := h) (q := q) (e := e) (u := F.map g) s l))) q
def normalizedLong :=
  front f (F.map e) m (F.map g) q ≪≫
    whiskerLeftIso f (crossed (foldMap F s) t a (foldUnit F l)) ≪≫
    (α_ f (F.map g) q).symm
theorem cutLong : longer F f g e h m n q s t a l = normalizedLong F f g e h m n q s t a l := by
  apply Iso.ext
  unfold longer
  rw [folded]
  simp only [startLong,normalizedLong,crossed,atom,finish,front,moveHead,moveTail,foldBare,expand,
    Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,whiskerRightIso_hom,whiskerRightIso_inv,
    whiskerLeftIso_hom,whiskerLeftIso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc,
    Iso.inv_hom_id_assoc,inv_hom_whiskerRight_assoc,whiskerLeft_inv_hom_assoc]
  simp only [foldMap,foldUnit,F.mapComp_eq_eqToIso,F.mapId_eq_eqToIso,Strict.associator_eqToIso,Strict.rightUnitor_eqToIso,Strict.leftUnitor_eqToIso,
    Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_hom,
    eqToIso.hom,eqToIso.inv,PrelaxFunctor.map₂Iso_hom,PrelaxFunctor.map₂Iso_inv,comp_whiskerRight,Bicategory.whiskerLeft_comp,
    comp_whiskerLeft,Bicategory.whiskerRight_comp,whisker_assoc,whiskerLeft_eqToHom,eqToHom_whiskerRight,Category.assoc,eqToHom_trans,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp,Category.comp_id]
def shorter := whiskerRightIso (whiskerRightIso ((α_ f (F.map e) m) ≪≫ whiskerLeftIso f r ≪≫ (ρ_ f)) (F.map g)) q
def normalizedShort :=
  front f (F.map e) m (F.map g) q ≪≫
    whiskerLeftIso f (whiskerRightIso (RepresentableTriangleCorner.direct (g := F.map g) r) q) ≪≫
    (α_ f (F.map g) q).symm
theorem cutShort : shorter F f g e m q r = normalizedShort F f g e m q r := by
  apply Iso.ext
  simp only [shorter,normalizedShort,front,RepresentableTriangleCorner.direct,Iso.trans_hom,Iso.symm_hom,
    whiskerRightIso_hom,whiskerLeftIso_hom,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  bicategory
end Generic
end ContextualComposition.GrothendieckStep.RepresentableTriangleFrame
