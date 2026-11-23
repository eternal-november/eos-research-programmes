module
public import ContextualComposition.EndpointBicategory
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Products.Basic

@[expose] public section
namespace ContextualComposition.Factorization.Endpoint.Indexed
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory Opposite
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable {C : Type uC} [Category.{vC} C]
variable (K : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vK,uK}) (L : LocallyDiscrete C ⥤ᵖ Cat.{vL,uL})
set_option backward.isDefEq.respectTransparency false
attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-- Inclusion of a fibre into the covariant total category; vertical arrows contain the chosen pseudofunctor unitor. -/
def outInclusion (B : C) : L.obj ⟨B⟩ ⥤ Pseudofunctor.Grothendieck L where
  obj Q := ⟨B,Q⟩
  map f := ⟨𝟙 B, (L.mapId ⟨B⟩).hom.toNatTrans.app _ ≫ f⟩
  map_comp f g := by
    ext
    · simp
    · simp [L.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso]

/-- The cleavage arrows of both total categories give the endpoint lifts before applying the extension functors. -/
def inputLift {A A' : C} (u : A' ⟶ A) :
    (K.map u.op.toLoc).toFunctor ⋙ Pseudofunctor.CoGrothendieck.ι K A' ⟶
      Pseudofunctor.CoGrothendieck.ι K A where
  app P := Pseudofunctor.CoGrothendieck.cartesianLift P u
  naturality {P P'} f := by
    ext
    · change 𝟙 _ ≫ u = u ≫ 𝟙 _
      simp
    · simp [Pseudofunctor.CoGrothendieck.ι, K.mapComp_id_right_inv_app, K.mapComp_id_left_inv_app,
        Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
      let i := (K.map u.op.toLoc).toFunctor.mapIso ((Cat.Hom.toNatIso (K.mapId ⟨op A⟩)).app P')
      erw [i.inv_hom_id_assoc]

def outputLift {B B' : C} (v : B ⟶ B') :
    outInclusion L B ⟶ (L.map v.toLoc).toFunctor ⋙ outInclusion L B' where
  app Q := ⟨v,𝟙 _⟩
  naturality {Q Q'} f := by
    ext
    · simp [outInclusion]
    · simp [outInclusion, L.mapComp_id_right_hom_app, L.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso,
        Strict.rightUnitor_eqToIso]
      rw [← Functor.map_comp_assoc, ← Cat.Hom₂.comp_app]
      simp

/-- The input component is the chosen strongly cartesian arrow of the contravariant Grothendieck construction. -/
theorem input_cartesian {A A' : C} (u : A' ⟶ A) (P : K.obj ⟨op A⟩) :
    Functor.IsStronglyCartesian (Pseudofunctor.CoGrothendieck.forget K) u ((inputLift K u).app P) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift P u

/-- Strong cocartesianness at a fixed base factorization. Arrows over the second leg correspond to their native fibre morphisms. -/
theorem output_cocartesian {A B D : C} (u : A ⟶ B) (v : B ⟶ D) (P : L.obj ⟨A⟩) (Z : L.obj ⟨D⟩)
    (h : (outInclusion L A).obj P ⟶ (outInclusion L D).obj Z) (hb : h.base = u ≫ v) :
    ∃! k : (L.map v.toLoc).toFunctor.obj ((L.map u.toLoc).toFunctor.obj P) ⟶ Z,
      (outputLift L u).app P ≫ (⟨v,k⟩ : Pseudofunctor.Grothendieck.Hom _ _) = h := by
  obtain ⟨base,t⟩ := h
  change base = u ≫ v at hb
  subst base
  let i := (Cat.Hom.toNatIso (L.mapComp u.toLoc v.toLoc)).app P
  refine ⟨i.inv ≫ t, ?_, ?_⟩
  · ext
    · rfl
    · erw [eqToHom_refl, Category.id_comp]
      change i.hom ≫ (L.map v.toLoc).toFunctor.map (𝟙 _) ≫ i.inv ≫ t = _
      simp
  · intro k hk
    have ht := Pseudofunctor.Grothendieck.Hom.congr hk
    change i.hom ≫ (L.map v.toLoc).toFunctor.map (𝟙 _) ≫ k = _ at ht
    simp at ht
    rw [← ht, i.inv_hom_id_assoc]

variable (e : Pseudofunctor.CoGrothendieck K ⥤ C) (d : Pseudofunctor.Grothendieck L ⥤ C)

theorem input_id (A : C) (P : K.obj ⟨op A⟩) :
    (Pseudofunctor.CoGrothendieck.ι K A).map ((K.mapId ⟨op A⟩).hom.toNatTrans.app P) =
      (inputLift K (𝟙 A)).app P := by
  ext
  · rfl
  · simp [Pseudofunctor.CoGrothendieck.ι, inputLift]

theorem output_id (B : C) (Q : L.obj ⟨B⟩) :
    (outputLift L (𝟙 B)).app Q ≫ (outInclusion L B).map ((L.mapId ⟨B⟩).hom.toNatTrans.app Q) =
      𝟙 ((outInclusion L B).obj Q) := by
  ext
  · simp [outputLift, outInclusion]
  · simp [outputLift, outInclusion, L.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso,
      ← Cat.Hom₂.comp_app]

theorem input_comp {A B D : C} (u : B ⟶ A) (v : D ⟶ B) (P : K.obj ⟨op A⟩) :
    (Pseudofunctor.CoGrothendieck.ι K D).map ((K.mapComp u.op.toLoc v.op.toLoc).hom.toNatTrans.app P) ≫
      (inputLift K v).app ((K.map u.op.toLoc).toFunctor.obj P) ≫ (inputLift K u).app P =
    (inputLift K (v ≫ u)).app P := by
  ext
  · simp [Pseudofunctor.CoGrothendieck.ι, inputLift]
  · simp [Pseudofunctor.CoGrothendieck.ι, inputLift, K.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso]
    have t := (K.mapId ⟨op D⟩).inv.toNatTrans.naturality ((K.mapComp u.op.toLoc v.op.toLoc).inv.toNatTrans.app P)
    erw [← reassoc_of% t]
    erw [(Cat.Hom.toNatIso (K.mapComp u.op.toLoc v.op.toLoc)).hom_inv_id_app_assoc]
    simp

theorem output_comp {A B D : C} (u : A ⟶ B) (v : B ⟶ D) (Q : L.obj ⟨A⟩) :
    (outputLift L (u ≫ v)).app Q ≫ (outInclusion L D).map ((L.mapComp u.toLoc v.toLoc).hom.toNatTrans.app Q) =
    (outputLift L u).app Q ≫ (outputLift L v).app ((L.map u.toLoc).toFunctor.obj Q) := by
  ext
  · simp [outputLift, outInclusion]
  · simp [outputLift, outInclusion, L.mapComp_id_right_hom_app, Strict.rightUnitor_eqToIso]

/-- The source presentation at a pair of endpoints, extracted from the two total extension functors. -/
def presentation (i : Cᵒᵖ × C) : Presentation.{vK,vL,vC,uK,uL,uC} C where
  input := K.obj ⟨i.1⟩
  output := L.obj ⟨i.2⟩
  source := Pseudofunctor.CoGrothendieck.ι K i.1.unop ⋙ e
  target := outInclusion L i.2 ⋙ d

def transport {i j : Cᵒᵖ × C} (p : i ⟶ j) :
    (presentation K L e d i) ⟶ (presentation K L e d j) where
  input := (K.map p.1.toLoc).toFunctor
  output := (L.map p.2.toLoc).toFunctor
  inputLift := whiskerRight (inputLift K p.1.unop) e
  outputLift := whiskerRight (outputLift L p.2) d

/-- The unit comparisons of the two indexing pseudofunctors preserve the actual extension arrows. -/
def identityChoice (i : Cᵒᵖ × C) :
    ChoiceIso (transport K L e d (𝟙 i)) (identityData (presentation K L e d i).source (presentation K L e d i).target) where
  input := Cat.Hom.toNatIso (K.mapId ⟨i.1⟩)
  output := Cat.Hom.toNatIso (L.mapId ⟨i.2⟩)
  input_lift P := by
    change e.map _ ≫ 𝟙 _ = e.map _
    rw [Category.comp_id]
    exact congrArg e.map (input_id K i.1.unop P)
  output_lift Q := by
    change d.map _ ≫ d.map _ = 𝟙 _
    erw [← d.map_comp, output_id L i.2 Q, d.map_id]

/-- The compositor of each grade pseudofunctor gives the comparison even when the extension of a cleavage arrow is noninvertible. -/
def compositionChoice {i j k : Cᵒᵖ × C} (p : i ⟶ j) (q : j ⟶ k) :
    ChoiceIso (transport K L e d (p ≫ q)) (composeData (transport K L e d p) (transport K L e d q)) where
  input := Cat.Hom.toNatIso (K.mapComp p.1.toLoc q.1.toLoc)
  output := Cat.Hom.toNatIso (L.mapComp p.2.toLoc q.2.toLoc)
  input_lift P := by
    change e.map _ ≫ (𝟙 _ ≫ e.map _ ≫ e.map _) = e.map _
    erw [Category.id_comp, ← e.map_comp, ← e.map_comp]
    exact congrArg e.map (input_comp K p.1.unop q.1.unop P)
  output_lift Q := by
    change d.map _ ≫ d.map _ = d.map _ ≫ d.map _ ≫ 𝟙 _
    erw [Category.comp_id, ← d.map_comp, ← d.map_comp]
    exact congrArg d.map (output_comp L p.2 q.2 Q)

end ContextualComposition.Factorization.Endpoint.Indexed
