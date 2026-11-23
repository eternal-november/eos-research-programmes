module
public import ContextualComposition.RelativeTensorOuterRow

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem strong_eq {A U : Type*} [Bicategory A] [Bicategory U] {F G : A ⥤ᵖ U}
    (s t : F ⟶ G) (ha : s.app = t.app) (hn : HEq (@s.naturality) (@t.naturality)) : s = t := by
  cases s; cases t; cases ha; cases hn; rfl

/-- An identity-on-fibres version of the row identification, computing on native vertices. -/
def rowId (a : LocallyDiscrete Bᵒᵖ) : row (middleComposite M N) a.as.unop ⟶ leftInner (row M a.as.unop) N where
  app _ := 𝟙 _
  naturality _ := Iso.refl _
  naturality_naturality m := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  naturality_id d := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change 𝟙 _ ≫ ((leftInner (row M a.as.unop) N).mapId d).hom.toNatTrans.app x =
      ((row (middleComposite M N) a.as.unop).mapId d).hom.toNatTrans.app x ≫ 𝟙 _ ≫ 𝟙 _
    rw [middleRow_unit M N a.as.unop d,Category.id_comp,Category.id_comp,Category.comp_id]
  naturality_comp f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change 𝟙 _ ≫ ((leftInner (row M a.as.unop) N).mapComp f g).hom.toNatTrans.app x =
      ((row (middleComposite M N) a.as.unop).mapComp f g).hom.toNatTrans.app x ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [middleRow_comp M N a.as.unop f g]
    simp
    congr 1
    apply Eq.symm
    apply Category.comp_id

private theorem map_id_of_eq {F G : LocallyDiscrete D ⥤ᵖ Cat.{vN,uN}}
    (h : F = G) (s : F ⟶ G) (W : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})
    (ha : HEq s.app (Pseudofunctor.StrongTrans.id F).app) (hn : HEq (@s.naturality) (@(Pseudofunctor.StrongTrans.id F).naturality)) :
    mapFirst s = (identifyFirst h W).functor := by
  subst G
  rw [strong_eq s (𝟙 F) (eq_of_heq ha) hn]
  exact First.map_identity

theorem map_rowId (a : LocallyDiscrete Bᵒᵖ) : mapFirst (G := Y) (rowId M N a) = normalize M N Y a := by
  apply map_id_of_eq (middleRow M N a.as.unop)
  · rfl
  · apply heq_of_eq
    funext i j f
    apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp

/-- The same row equivalence, now computing on native arrows without a whole-diagram cast. -/
def direct (a : LocallyDiscrete Bᵒᵖ) : source M N Y a ⥤ target M N Y a := mapFirst (G := Y) (rowId M N a) ⋙ rebracket M N Y a

theorem direct_eq (a : LocallyDiscrete Bᵒᵖ) : direct M N Y a = component M N Y a :=
  congrArg (· ⋙ rebracket M N Y a) (map_rowId M N Y a)

theorem direct_naturality {a b : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) :
    changeSource M N Y u ⋙ direct M N Y b = direct M N Y a ⋙ changeTarget M N Y u :=
  (congrArg (changeSource M N Y u ⋙ ·) (direct_eq M N Y b)).trans
    ((naturality M N Y u).trans (congrArg (· ⋙ changeTarget M N Y u) (direct_eq M N Y a)).symm)

theorem direct_transport {a b : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (z : source M N Y a) :
    (eqToHom (direct_naturality M N Y u)).app z = 𝟙 _ := by
  rw [eqToHom_app]; rfl

end ContextualComposition.RelativeTensor.Iterated.OuterRow
