module
public import ContextualComposition.RelativeTensorCurried
public import ContextualComposition.RelativeTensorAssociator
public import ContextualComposition.IndexedNormalization

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

section Precomp
universe w v u w' v' u' w'' v'' u''
variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B] {D : Type u''} [Bicategory.{w'',v''} D]
variable (H : A ⥤ᵖ B)
open Factorization.Endpoint.Indexed

/-- Reindex whole Cat-valued or bicategory-valued action diagrams by the given weak index functor. -/
def precompose : Pseudofunctor (B ⥤ᵖ D) (A ⥤ᵖ D) where
  obj := H.comp
  map := reindex H
  map₂ := reindexCell H
  mapId F := Iso.refl _
  mapComp s t := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by
    intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro x
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp,Category.comp_id]
    rfl
  map₂_whisker_right := by
    intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro x
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp,Category.comp_id]
    rfl
  map₂_associator := by
    intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro x
    simp
    erw [Bicategory.whiskerLeft_id,Category.id_comp,Category.comp_id]
    rfl
  map₂_left_unitor := by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro x; simp; rfl
  map₂_right_unitor := by intros; apply Pseudofunctor.StrongTrans.homCategory.ext; intro x; simp; rfl
end Precomp

section Four
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Form the middle two-factor module, varying both of its exposed indices independently. -/
def middleComposite := (N.comp Parametric.curried).comp (precompose (Middle.transpose M))
abbrev farLeft := Left (leftInner X M) N Y
abbrev innerLeft := Left X (middleComposite M N) Y
abbrev opposedPairs := Tensor (leftInner X M) (rightInner N Y)
abbrev innerRight := Right X (middleComposite M N) Y
abbrev farRight := Right X M (rightInner N Y)

/-- The two-step route reassociates first at the second junction and then at the first, retaining the two separated pairs at its midpoint. -/
def twoStep : farLeft X M N Y ≌ farRight X M N Y :=
  (associator (leftInner X M) N Y).trans (associator X M (rightInner N Y))

end Four
end ContextualComposition.RelativeTensor.Iterated
