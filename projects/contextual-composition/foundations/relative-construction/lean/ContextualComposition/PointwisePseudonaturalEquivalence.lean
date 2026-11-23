module
public import ContextualComposition.PointwisePseudonaturalInverse
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

@[expose] public section
namespace ContextualComposition.PseudonaturalInverse
open CategoryTheory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe w v u v' u'
variable {A : Type u} [Bicategory.{w,v} A] {F G : A ⥤ᵖ Cat.{v',u'}}
variable (η : F ⟶ G) [∀ a, (η.app a).toFunctor.IsEquivalence]
set_option backward.isDefEq.respectTransparency false

private theorem unitPasting {D : Type*} [Category* D] {a b c d : D} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : a ⟶ d) (e : f ≫ g ≫ h = k) : f ≫ 𝟙 _ ≫ g ≫ 𝟙 _ ≫ h ≫ 𝟙 _ = (𝟙 _ ≫ 𝟙 _) ≫ k := by simpa using e
private theorem counitPasting {D : Type*} [Category* D] {a b c d : D} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : a ⟶ d) (e : f ≫ g ≫ h = k) : k ≫ (𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ f ≫ 𝟙 _ ≫ g ≫ 𝟙 _) ≫ h := by
  simpa [Category.assoc] using e.symm

noncomputable def unit : 𝟙 F ≅ η ≫ inverse η :=
  Pseudofunctor.StrongTrans.isoMk (fun a => Cat.Hom.isoMk (fibre η a).unitIso) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact unitPasting _ _ _ _ (recoverySquare_unit (fibre η a) (fibre η b) _ _ (square η f) x))

noncomputable def counit : inverse η ≫ η ≅ 𝟙 G :=
  Pseudofunctor.StrongTrans.isoMk (fun a => Cat.Hom.isoMk (fibre η a).counitIso) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact counitPasting _ _ _ _ (recoverySquare_counit (fibre η a) (fibre η b) _ _ (square η f) x))

private theorem triangleShape {D : Type*} [Bicategory D] {a b : D} {f : a ⟶ b} {g : b ⟶ a}
    (n : 𝟙 a ≅ f ≫ g) (e : g ≫ f ≅ 𝟙 b) :
    (Bicategory.leftZigzagIso n e).hom = n.hom ▷ f ≫ (α_ f g f).hom ≫ f ◁ e.hom := by
  dsimp only [Bicategory.leftZigzagIso, bicategoricalIsoComp, Iso.trans_hom]
  congr 1
  congr 1
  bicategory_coherence

private theorem trianglePasting {D : Type*} [Category* D] {a b : D} (f : a ⟶ b) (g : b ⟶ a) (h : f ≫ g = 𝟙 a) :
    f ≫ 𝟙 _ ≫ g = 𝟙 _ ≫ 𝟙 a := by simpa using h

/-- A componentwise equivalence of Cat-valued pseudofunctors is an adjoint equivalence with the original strong transformation as its forward 1-cell. -/
noncomputable def equivalence : Bicategory.Equivalence F G where
  hom := η
  inv := inverse η
  unit := unit η
  counit := counit η
  left_triangle := by
    apply Iso.ext
    rw [triangleShape]
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    exact trianglePasting _ _ ((fibre η a).functor_unitIso_comp x)

end ContextualComposition.PseudonaturalInverse
