module
public import ContextualComposition.RelativeTensorIterates
public import ContextualComposition.RelativeTensorLeftUnit
public import ContextualComposition.RelativeTensorRightUnit

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u
variable {B : Type u} [Category.{v} B]

/-- Postcomposition changes the represented column of the identity bimodule. -/
def unitPostcompose {a b : B} (u : a ⟶ b) : RightUnit.represented a ⟶ RightUnit.represented b where
  app i := typeToCat.map ((yoneda.map u).app i.as)
  naturality {i j} f := Cat.Hom.isoMk (NatIso.ofComponents (fun p => eqToIso (by
    change Discrete.mk ((f.as.unop ≫ p.as) ≫ u) = Discrete.mk (f.as.unop ≫ (p.as ≫ u))
    rw [Category.assoc])) (by intros; apply Discrete.hom_eq))
  naturality_naturality m := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq
  naturality_id i := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq
  naturality_comp f g := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq

def unitPostcomposeId (a : B) : unitPostcompose (𝟙 a) ≅ 𝟙 (RightUnit.represented a) :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (NatIso.ofComponents (fun p => eqToIso (by
    change Discrete.mk (p.as ≫ 𝟙 a) = Discrete.mk p.as
    rw [Category.comp_id])) (by intros; apply Discrete.hom_eq))) (by
    intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq)

def unitPostcomposeComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    unitPostcompose (f ≫ g) ≅ unitPostcompose f ≫ unitPostcompose g :=
  Pseudofunctor.StrongTrans.isoMk (fun i => Cat.Hom.isoMk (NatIso.ofComponents (fun p => eqToIso (by
    change Discrete.mk (p.as ≫ (f ≫ g)) = Discrete.mk ((p.as ≫ f) ≫ g)
    rw [Category.assoc])) (by intros; apply Discrete.hom_eq))) (by
    intros; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq)

/-- The ordinary hom bifunctor as a weak curried module with discrete arrow fibres. -/
def unitModule (B : Type u) [Category.{v} B] :
    LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{_,_}) :=
  LocallyDiscrete.mkPseudofunctor (fun b => RightUnit.represented b) (fun f => unitPostcompose f)
    unitPostcomposeId unitPostcomposeComp
    (by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro i; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq)
    (by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro i; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq)
    (by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro i; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply Discrete.hom_eq)

theorem unitModule_column (b : B) : column (unitModule B) b = RightUnit.represented b := rfl

end ContextualComposition.RelativeTensor.Iterated
