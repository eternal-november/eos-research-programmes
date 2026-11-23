module
public import ContextualComposition.RelativeTensorOuterRowArrow

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe v u

private theorem eraseLeft {D : Type*} [Category* D] {a b c : D} (e : a = b) (g : b ⟶ c) :
    pack (eqToHom e ≫ g) = pack g := by subst b; simp

private theorem eraseRight {D : Type*} [Category* D] {a b c d : D} (f : a ⟶ b) (e : b = c) (h : c = d) :
    pack (f ≫ eqToHom e ≫ eqToHom h) = pack f := by subst c; subst d; simp

private theorem unitSquare {D : Type*} [Category* D] {a b c : D} (e : a = b) (g : b ⟶ c) (f : a ⟶ c) (h : pack f = pack g) :
    eqToHom e ≫ g = f := pack_injective ((eraseLeft e g).trans h.symm)

private theorem compSquare {D : Type*} [Category* D] {a b c d e : D} (i : a = b) (g : b ⟶ c)
    (f : a ⟶ d) (j : d = e) (k : e = c) (h : pack f = pack g) :
    eqToHom i ≫ g = f ≫ eqToHom j ≫ eqToHom k :=
  pack_injective ((eraseLeft i g).trans (h.symm.trans (eraseRight f j k).symm))

/-- Package commuting component functors as a strong transformation once the two actual weak-action structure arrows agree with their endpoints retained. -/
def strongOfSquares {I : Type*} [Category* I] (F G : LocallyDiscrete I ⥤ᵖ Cat.{v,u}) (E : ∀ a, F.obj a ⥤ G.obj a)
    (sq : ∀ {a b} (f : a ⟶ b), (F.map f).toFunctor ⋙ E b = E a ⋙ (G.map f).toFunctor)
    (one : ∀ a x, pack ((E a).map ((F.mapId a).hom.toNatTrans.app x)) = pack ((G.mapId a).hom.toNatTrans.app ((E a).obj x)))
    (two : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c) x,
      pack ((E c).map ((F.mapComp f g).hom.toNatTrans.app x)) = pack ((G.mapComp f g).hom.toNatTrans.app ((E a).obj x))) : F ⟶ G where
  app a := (E a).toCatHom
  naturality f := Cat.Hom.isoMk (eqToIso (sq f))
  naturality_naturality {a b f g} m := by
    obtain rfl := LocallyDiscrete.eq_of_hom m
    obtain rfl := Subsingleton.elim m (𝟙 f)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (E b).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.map_id,Category.id_comp,Category.comp_id]
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (eqToHom (sq (𝟙 a))).app x ≫ (G.mapId a).hom.toNatTrans.app ((E a).obj x) =
      (E a).map ((F.mapId a).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [eqToHom_app,Category.comp_id]
    exact unitSquare _ _ _ (one a x)
  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (eqToHom (sq (f ≫ g))).app x ≫ (G.mapComp f g).hom.toNatTrans.app ((E a).obj x) =
      (E c).map ((F.mapComp f g).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
      (eqToHom (sq g)).app ((F.map f).toFunctor.obj x) ≫ 𝟙 _ ≫
      (G.map g).toFunctor.map ((eqToHom (sq f)).app x) ≫ 𝟙 _
    simp only [eqToHom_app,Category.id_comp,Category.comp_id,eqToHom_map]
    exact compSquare _ _ _ _ _ (two f g x)

end ContextualComposition.RelativeTensor.Iterated.OuterRow
