module
public import ContextualComposition.RelativeTensorComma
public import ContextualComposition.RelativeTensorBifunctor

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable {K K' : Type uK} {L L' : Type uL} {C : Type uC}
variable [Category.{vK} K] [Category.{vK} K'] [Category.{vL} L] [Category.{vL} L'] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}
variable (T : Endpoint.Data e d e' d')
set_option backward.isDefEq.respectTransparency false

def inputAt (i : C) : CostructuredArrow e i ⥤ CostructuredArrow e' i where
  obj x := CostructuredArrow.mk (T.inputLift.app x.left ≫ x.hom)
  map {x y} f := CostructuredArrow.homMk (T.input.map f.left) (by
    change e'.map (T.input.map f.left) ≫ T.inputLift.app y.left ≫ y.hom = _
    erw [← Category.assoc,T.inputLift.naturality,Category.assoc,CostructuredArrow.w]
    rfl)
  map_id _ := by apply CostructuredArrow.hom_ext; exact T.input.map_id _
  map_comp f g := by apply CostructuredArrow.hom_ext; exact T.input.map_comp _ _

def outputAt (i : C) : StructuredArrow i d ⥤ StructuredArrow i d' where
  obj y := StructuredArrow.mk (y.hom ≫ T.outputLift.app y.right)
  map {x y} f := StructuredArrow.homMk (T.output.map f.right) (by
    change (x.hom ≫ T.outputLift.app x.right) ≫ d'.map (T.output.map f.right) = _
    erw [Category.assoc,← T.outputLift.naturality,← Category.assoc,StructuredArrow.w]
    rfl)
  map_id _ := by apply StructuredArrow.hom_ext; exact T.output.map_id _
  map_comp f g := by apply StructuredArrow.hom_ext; exact T.output.map_comp _ _

def inputSquare {i j : C} (u : i ⟶ j) :
    CostructuredArrow.map u ⋙ inputAt T j ≅ inputAt T i ⋙ CostructuredArrow.map u :=
  NatIso.ofComponents (fun x => CostructuredArrow.isoMk (Iso.refl (T.input.obj x.left)) (by
    change e'.map (𝟙 _) ≫ ((T.inputLift.app x.left ≫ x.hom) ≫ u) = T.inputLift.app x.left ≫ x.hom ≫ u
    simp)) (by
    intro x y f; apply CostructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def outputSquare {i j : C} (u : i ⟶ j) :
    StructuredArrow.map u ⋙ outputAt T i ≅ outputAt T j ⋙ StructuredArrow.map u :=
  NatIso.ofComponents (fun y => StructuredArrow.isoMk (Iso.refl (T.output.obj y.right)) (by
    change ((u ≫ y.hom) ≫ T.outputLift.app y.right) ≫ d'.map (𝟙 _) = u ≫ y.hom ≫ T.outputLift.app y.right
    simp)) (by
    intro x y f; apply StructuredArrow.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private theorem discrete_id {A : Type*} [Category* A] {i j : LocallyDiscrete A} {p q : i ⟶ j} (f : p ⟶ q) :
    ∃ h : p = q, f = eqToHom h := ⟨Discrete.ext (Discrete.eq_of_hom f),Subsingleton.elim _ _⟩

def inputComparison : Pseudofunctor.StrongTrans (input e) (input e') where
  app i := (inputAt T i.as).toCatHom
  naturality u := Cat.Hom.isoMk (inputSquare T u.as)
  naturality_naturality m := by
    obtain ⟨rfl,rfl⟩ := discrete_id m
    simp
  naturality_id i := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext
    change 𝟙 _ ≫ (((input e').mapId i).hom.toNatTrans.app ((inputAt T i.as).obj x)).left =
      T.input.map (((input e).mapId i).hom.toNatTrans.app x).left ≫ 𝟙 _ ≫ 𝟙 _
    simp only [input,Functor.toPseudofunctor'_mapId,eqToIso.hom,Cat.eqToHom_app]
    erw [CostructuredArrow.eqToHom_left,CostructuredArrow.eqToHom_left,eqToHom_refl,eqToHom_refl,Functor.map_id,Category.id_comp,Category.id_comp]
  naturality_comp u v := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply CostructuredArrow.hom_ext
    change 𝟙 _ ≫ (((input e').mapComp u v).hom.toNatTrans.app ((inputAt T _).obj x)).left =
      T.input.map (((input e).mapComp u v).hom.toNatTrans.app x).left ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [input,Functor.toPseudofunctor'_mapComp,eqToIso.hom,Cat.eqToHom_app]
    erw [CostructuredArrow.eqToHom_left,CostructuredArrow.eqToHom_left,eqToHom_refl,eqToHom_refl,Functor.map_id]
    simp
    rfl

def outputComparison : Pseudofunctor.StrongTrans (output d) (output d') where
  app i := (outputAt T i.as.unop).toCatHom
  naturality u := Cat.Hom.isoMk (outputSquare T u.as.unop)
  naturality_naturality m := by
    obtain ⟨rfl,rfl⟩ := discrete_id m
    simp
  naturality_id i := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext
    change 𝟙 _ ≫ (((output d').mapId i).hom.toNatTrans.app ((outputAt T i.as.unop).obj x)).right =
      T.output.map (((output d).mapId i).hom.toNatTrans.app x).right ≫ 𝟙 _ ≫ 𝟙 _
    simp only [output,Functor.toPseudofunctor'_mapId,eqToIso.hom,Cat.eqToHom_app]
    erw [StructuredArrow.eqToHom_right,StructuredArrow.eqToHom_right,eqToHom_refl,eqToHom_refl,Functor.map_id,Category.id_comp,Category.id_comp]
  naturality_comp u v := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x; apply StructuredArrow.hom_ext
    change 𝟙 _ ≫ (((output d').mapComp u v).hom.toNatTrans.app ((outputAt T _).obj x)).right =
      T.output.map (((output d).mapComp u v).hom.toNatTrans.app x).right ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [output,Functor.toPseudofunctor'_mapComp,eqToIso.hom,Cat.eqToHom_app]
    erw [StructuredArrow.eqToHom_right,StructuredArrow.eqToHom_right,eqToHom_refl,eqToHom_refl,Functor.map_id]
    simp
    rfl

def tensorTransport : Carrier e d ⥤ Carrier e' d' := mapBoth (inputComparison T) (outputComparison T)

end ContextualComposition.RelativeTensor.Presented
