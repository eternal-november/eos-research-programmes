module
public import ContextualComposition.RelativeTensorFourFactors
@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vD uD vX uX vM uM
variable {B : Type u} [Category.{v} B] {D : Type uD} [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable {P Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})} (s : P ⟶ Q)
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The square uses the two second-factor compositors and the supplied strong naturality isomorphism. -/
def crossingSquare {a b : LocallyDiscrete D} (u : a ⟶ b) :
    (leftInner X P).map u ≫ (mapSecond (F := X) (s.app b)).toCatHom ≅ (mapSecond (F := X) (s.app a)).toCatHom ≫ (leftInner X Q).map u :=
  (Second.compositeIso X (P.map u) (s.app b)).symm ≪≫ (Second.action X).map₂Iso (s.naturality u) ≪≫ Second.compositeIso X (s.app a) (Q.map u)

theorem crossingSquare_app {a b : LocallyDiscrete D} (u : a ⟶ b) (z : Tensor X (P.obj a)) :
    (crossingSquare X s u).hom.toNatTrans.app z = (insertion X (Q.obj b) z.as.mid).map
      (productMap (𝟙 z.as.first) (((s.naturality u).hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)) := by
  change (Second.compositeIso X (P.map u) (s.app b)).inv.toNatTrans.app z ≫
    (Second.mapCell (F := X) (s.naturality u).hom.as).app z ≫ (Second.compositeIso X (s.app a) (Q.map u)).hom.toNatTrans.app z = _
  rw [Second.composite_inv_app,Second.composite_hom_app,Category.id_comp]
  exact Category.comp_id _

private theorem one {R : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})} (a : LocallyDiscrete D) (z : Tensor X (R.obj a)) :
    ((leftInner X R).mapId a).hom.toNatTrans.app z = (insertion X (R.obj a) z.as.mid).map
      (productMap (𝟙 z.as.first) (((R.mapId a).hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)) := by
  change (Second.mapCell (F := X) (R.mapId a).hom.as).app z ≫ (Second.identityIso X (R.obj a)).hom.toNatTrans.app z = _
  rw [Second.identity_hom_app]
  exact Category.comp_id _

private theorem two {R : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})} {a b c : LocallyDiscrete D} (u : a ⟶ b) (v : b ⟶ c) (z : Tensor X (R.obj a)) :
    ((leftInner X R).mapComp u v).hom.toNatTrans.app z = (insertion X (R.obj c) z.as.mid).map
      (productMap (𝟙 z.as.first) (((R.mapComp u v).hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)) := by
  change (Second.mapCell (F := X) (R.mapComp u v).hom.as).app z ≫ (Second.compositeIso X (R.map u) (R.map v)).hom.toNatTrans.app z = _
  rw [Second.composite_hom_app]
  exact Category.comp_id _

private abbrev coord {U V : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}} {h k : U ⟶ V} (a : h ⟶ k) {i : B} (y : U.obj ⟨op i⟩) :=
  (a.as.app ⟨op i⟩).toNatTrans.app y

private abbrev insertAt (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}) {b : B} (x : X.obj ⟨b⟩) :=
  CategoryTheory.Prod.sectR x (G.obj ⟨op b⟩) ⋙ insertion X G b

/-- Apply the second-factor tensor action to a supplied strong comparison of curried modules. -/
def crossingPayload : leftInner X P ⟶ leftInner X Q where
  app a := (mapSecond (F := X) (s.app a)).toCatHom
  naturality := crossingSquare X s
  naturality_naturality {a b f g} n := by
    obtain rfl := LocallyDiscrete.eq_of_hom n
    obtain rfl := Subsingleton.elim n (𝟙 f)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (crossingSquare X s (𝟙 a)).hom.toNatTrans.app z ≫ ((leftInner X Q).mapId a).hom.toNatTrans.app _ =
      (mapSecond (F := X) (s.app a)).map (((leftInner X P).mapId a).hom.toNatTrans.app z) ≫ 𝟙 _ ≫ 𝟙 _
    rw [crossingSquare_app,one,one,Second.on_native,Category.id_comp,Category.comp_id]
    let J := insertAt X (Q.obj a) z.as.first
    let y := z.as.second
    let Sa := Second.part (s.app a) z.as.mid
    have h := congrArg (fun t => (t.as.app ⟨op z.as.mid⟩).toNatTrans.app y) (s.naturality_id a)
    change coord (s.naturality (𝟙 a)).hom y ≫ coord (Q.mapId a).hom (Sa.obj y) = Sa.map (coord (P.mapId a).hom y) ≫ 𝟙 _ ≫ 𝟙 _ at h
    simp only [Category.comp_id] at h
    exact (J.map_comp _ _).symm.trans (congrArg J.map h)
  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (crossingSquare X s (f ≫ g)).hom.toNatTrans.app z ≫ ((leftInner X Q).mapComp f g).hom.toNatTrans.app _ =
      (mapSecond (F := X) (s.app c)).map (((leftInner X P).mapComp f g).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
      (crossingSquare X s g).hom.toNatTrans.app _ ≫ 𝟙 _ ≫ (mapSecond (F := X) (Q.map g)).map ((crossingSquare X s f).hom.toNatTrans.app z) ≫ 𝟙 _
    simp only [crossingSquare_app,two,Category.id_comp,Category.comp_id]
    erw [Second.on_native (F := X) (s.app c),Second.on_native (F := X) (Q.map g)]
    let J := insertAt X (Q.obj c) z.as.first
    let y := z.as.second
    let Sa := Second.part (s.app a) z.as.mid
    let Sc := Second.part (s.app c) z.as.mid
    let Pf := Second.part (P.map f) z.as.mid
    let Qg := Second.part (Q.map g) z.as.mid
    have h := congrArg (fun t => (t.as.app ⟨op z.as.mid⟩).toNatTrans.app y) (s.naturality_comp f g)
    change coord (s.naturality (f ≫ g)).hom y ≫ coord (Q.mapComp f g).hom (Sa.obj y) =
      Sc.map (coord (P.mapComp f g).hom y) ≫ 𝟙 _ ≫ coord (s.naturality g).hom (Pf.obj y) ≫ 𝟙 _ ≫
        Qg.map (coord (s.naturality f).hom y) ≫ 𝟙 _ at h
    simp only [Category.id_comp,Category.comp_id] at h
    have m := congrArg J.map h
    simp only [Functor.map_comp] at m
    exact m
@[simp] theorem crossingPayload_app (a : LocallyDiscrete D) :
    (crossingPayload X s).app a = (mapSecond (F := X) (s.app a)).toCatHom := rfl

section Mixed
universe vN uN
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})) (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))

/-- A specified crossing of hom-indexed bimodules induces the corresponding strong map of their left-inner payload actions. -/
def liftCrossing (s : middleComposite N M ⟶ middleComposite M N) :
    leftInner X (middleComposite N M) ⟶ leftInner X (middleComposite M N) :=
  crossingPayload X s

end Mixed
end ContextualComposition.RelativeTensor.Iterated
