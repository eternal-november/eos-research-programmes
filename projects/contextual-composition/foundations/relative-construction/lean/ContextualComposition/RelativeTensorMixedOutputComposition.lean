module
public import ContextualComposition.RelativeTensorMixedOutputIdentity

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section Square
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
variable [Category* A₀] [Category* A₁] [Category* A₂] [Category* B₀] [Category* B₁] [Category* B₂]
variable {u₁ : A₀ ⥤ A₁} {u₂ : A₁ ⥤ A₂} {u₃ : A₀ ⥤ A₂}
variable {v₁ : B₀ ⥤ B₁} {v₂ : B₁ ⥤ B₂} {v₃ : B₀ ⥤ B₂}
variable {F₀ : A₀ ⥤ B₀} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂}

/-- Composition equation for three comparison squares with supplied action compositors.
The direct transition is compared to the successive transitions, not identified with them. -/
def RespectsEndpointComposition
    (σ₁ : u₁ ⋙ F₁ ≅ F₀ ⋙ v₁) (σ₂ : u₂ ⋙ F₂ ≅ F₁ ⋙ v₂)
    (σ₃ : u₃ ⋙ F₂ ≅ F₀ ⋙ v₃) (α : u₃ ⟶ u₁ ⋙ u₂) (β : v₃ ⟶ v₁ ⋙ v₂) : Prop :=
  ∀ z, σ₃.hom.app z ≫ β.app (F₀.obj z) =
    F₂.map (α.app z) ≫ σ₂.hom.app (u₁.obj z) ≫ v₂.map (σ₁.hom.app z)

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
variable {w₁ : C₀ ⥤ C₁} {w₂ : C₁ ⥤ C₂} {w₃ : C₀ ⥤ C₂}
variable {G₀ : B₀ ⥤ C₀} {G₁ : B₁ ⥤ C₁} {G₂ : B₂ ⥤ C₂}

theorem pasteEndpointComposition
    {σ₁ : u₁ ⋙ F₁ ≅ F₀ ⋙ v₁} {σ₂ : u₂ ⋙ F₂ ≅ F₁ ⋙ v₂} {σ₃ : u₃ ⋙ F₂ ≅ F₀ ⋙ v₃}
    {τ₁ : v₁ ⋙ G₁ ≅ G₀ ⋙ w₁} {τ₂ : v₂ ⋙ G₂ ≅ G₁ ⋙ w₂} {τ₃ : v₃ ⋙ G₂ ≅ G₀ ⋙ w₃}
    {α : u₃ ⟶ u₁ ⋙ u₂} {β : v₃ ⟶ v₁ ⋙ v₂} {γ : w₃ ⟶ w₁ ⋙ w₂}
    (hs : RespectsEndpointComposition σ₁ σ₂ σ₃ α β)
    (ht : RespectsEndpointComposition τ₁ τ₂ τ₃ β γ) :
    RespectsEndpointComposition (pasteInputSquare σ₁ τ₁) (pasteInputSquare σ₂ τ₂)
      (pasteInputSquare σ₃ τ₃) α γ := by
  intro z
  change (G₂.map (σ₃.hom.app z) ≫ τ₃.hom.app (F₀.obj z)) ≫ γ.app (G₀.obj (F₀.obj z)) =
    G₂.map (F₂.map (α.app z)) ≫
      (G₂.map (σ₂.hom.app (u₁.obj z)) ≫ τ₂.hom.app (F₁.obj (u₁.obj z))) ≫
      w₂.map (G₁.map (σ₁.hom.app z) ≫ τ₁.hom.app (F₀.obj z))
  have hn : G₂.map (v₂.map (σ₁.hom.app z)) ≫ τ₂.hom.app (v₁.obj (F₀.obj z)) =
      τ₂.hom.app (F₁.obj (u₁.obj z)) ≫ w₂.map (G₁.map (σ₁.hom.app z)) :=
    τ₂.hom.naturality (σ₁.hom.app z)
  rw [Category.assoc, ht, ← Category.assoc, ← G₂.map_comp, hs]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hn]

theorem reverseInputSquare_hom_app (E₀ : A₀ ≌ B₀) (E₁ : A₁ ≌ B₁)
    (σ : u₁ ⋙ E₁.functor ≅ E₀.functor ⋙ v₁) (z : B₀) :
    (reverseInputSquare E₀ E₁ σ).hom.app z =
      E₁.inverse.map (v₁.map (E₀.counitIso.inv.app z) ≫ σ.inv.app (E₀.inverse.obj z)) ≫
        E₁.unitIso.inv.app (u₁.obj (E₀.inverse.obj z)) := by
  simp only [reverseInputSquare, Iso.compInverseIso, Iso.isoInverseComp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.associator_hom_app, Iso.symm_hom,
    Category.id_comp]
  erw [Category.comp_id]
  rfl

theorem reverseInputSquare_counit (E₀ : A₀ ≌ B₀) (E₁ : A₁ ≌ B₁)
    (σ : u₁ ⋙ E₁.functor ≅ E₀.functor ⋙ v₁) (z : B₀) :
    E₁.functor.map ((reverseInputSquare E₀ E₁ σ).hom.app z) ≫ σ.hom.app (E₀.inverse.obj z) ≫
      v₁.map (E₀.counitIso.hom.app z) = E₁.counitIso.hom.app (v₁.obj z) := by
  rw [reverseInputSquare_hom_app]
  let q := v₁.map (E₀.counitIso.inv.app z) ≫ σ.inv.app (E₀.inverse.obj z)
  change E₁.functor.map (E₁.inverse.map q ≫ E₁.unitIso.inv.app _) ≫ _ = _
  have he : E₁.functor.map (E₁.unitIso.inv.app (u₁.obj (E₀.inverse.obj z))) =
      E₁.counitIso.hom.app (E₁.functor.obj (u₁.obj (E₀.inverse.obj z))) := (E₁.counit_app_functor _).symm
  have hn := E₁.counitIso.hom.naturality q
  change E₁.functor.map (E₁.inverse.map q) ≫ E₁.counitIso.hom.app (E₁.functor.obj (u₁.obj (E₀.inverse.obj z))) = E₁.counitIso.hom.app (v₁.obj z) ≫ q at hn
  rw [Functor.map_comp, he, hn]
  dsimp only [q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  exact Category.comp_id _

/-- Taking the inverse-equivalence mates of coherent squares preserves composition. -/
theorem reverseEndpointComposition (E₀ : A₀ ≌ B₀) (E₁ : A₁ ≌ B₁) (E₂ : A₂ ≌ B₂)
    {σ₁ : u₁ ⋙ E₁.functor ≅ E₀.functor ⋙ v₁} {σ₂ : u₂ ⋙ E₂.functor ≅ E₁.functor ⋙ v₂}
    {σ₃ : u₃ ⋙ E₂.functor ≅ E₀.functor ⋙ v₃}
    {α : u₃ ⟶ u₁ ⋙ u₂} {β : v₃ ⟶ v₁ ⋙ v₂}
    (h : RespectsEndpointComposition σ₁ σ₂ σ₃ α β) :
    RespectsEndpointComposition (reverseInputSquare E₀ E₁ σ₁) (reverseInputSquare E₁ E₂ σ₂)
      (reverseInputSquare E₀ E₂ σ₃) β α := by
  intro z
  let L := E₂.functor
  let x := E₀.inverse.obj z
  let ρ₁ := (reverseInputSquare E₀ E₁ σ₁).hom.app z
  let ρ₂ := (reverseInputSquare E₁ E₂ σ₂).hom.app (v₁.obj z)
  let ρ₃ := (reverseInputSquare E₀ E₂ σ₃).hom.app z
  let ε := E₀.counitIso.hom.app z
  let ε₁ := E₁.counitIso.hom.app (v₁.obj z)
  let ε₂ := E₂.counitIso.hom.app
  let k := σ₂.hom.app (u₁.obj x) ≫ v₂.map (σ₁.hom.app x) ≫ v₂.map (v₁.map ε)
  have : IsIso k := by dsimp only [k, x, ε]; infer_instance
  apply L.map_injective
  apply (cancel_mono k).mp
  change L.map (ρ₃ ≫ α.app x) ≫ k =
    L.map (E₂.inverse.map (β.app z) ≫ ρ₂ ≫ u₂.map ρ₁) ≫ k
  have hα := h x
  have hβ : β.app (E₀.functor.obj x) ≫ v₂.map (v₁.map ε) = v₃.map ε ≫ β.app z :=
    (β.naturality ε).symm
  have hn : L.map (u₂.map ρ₁) ≫ σ₂.hom.app (u₁.obj x) =
      σ₂.hom.app (E₁.inverse.obj (v₁.obj z)) ≫ v₂.map (E₁.functor.map ρ₁) :=
    σ₂.hom.naturality ρ₁
  have hε₂ : L.map (E₂.inverse.map (β.app z)) ≫ ε₂ (v₂.obj (v₁.obj z)) =
      ε₂ (v₃.obj z) ≫ β.app z := E₂.counitIso.hom.naturality (β.app z)
  have hc₁ : E₁.functor.map ρ₁ ≫ σ₁.hom.app x ≫ v₁.map ε = ε₁ := reverseInputSquare_counit E₀ E₁ σ₁ z
  have hc₂ : L.map ρ₂ ≫ σ₂.hom.app (E₁.inverse.obj (v₁.obj z)) ≫ v₂.map ε₁ =
      ε₂ (v₂.obj (v₁.obj z)) := reverseInputSquare_counit E₁ E₂ σ₂ (v₁.obj z)
  have hc₃ : L.map ρ₃ ≫ σ₃.hom.app x ≫ v₃.map ε = ε₂ (v₃.obj z) := reverseInputSquare_counit E₀ E₂ σ₃ z
  calc
    L.map (ρ₃ ≫ α.app x) ≫ k = ε₂ (v₃.obj z) ≫ β.app z := by
      dsimp only [k]
      rw [Functor.map_comp, Category.assoc, ← reassoc_of% hα, hβ, reassoc_of% hc₃]
    _ = L.map (E₂.inverse.map (β.app z) ≫ ρ₂ ≫ u₂.map ρ₁) ≫ k := by
      dsimp only [k]
      simp only [Functor.map_comp, Category.assoc, reassoc_of% hn]
      rw [← v₂.map_comp, ← v₂.map_comp, hc₁, hc₂, hε₂]

end Square

section TensorComposition
universe v u vX uX vM uM vN uN vY uY
variable {B : Type u} [Category.{v} B]
variable {Y₀ Y₁ Y₂ : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
variable {t₁ : Y₀ ⟶ Y₁} {t₂ : Y₁ ⟶ Y₂} {t₃ : Y₀ ⟶ Y₂}
variable (p : t₃ ⟶ t₁ ≫ t₂)
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))

/-- The second-factor action applies its own compositor after lifting the supplied cell. -/
def tensorLastComp : mapSecond (F := X) t₃ ⟶ mapSecond (F := X) t₁ ⋙ mapSecond (F := X) t₂ :=
  Second.mapCell (F := X) p.as ≫ (Second.compositeIso X t₁ t₂).hom.toNatTrans

theorem tensorLastComp_app (z : Tensor X Y₀) :
    (tensorLastComp p X).app z = (Second.mapCell (F := X) p.as).app z := by
  change _ ≫ (Second.compositeIso X t₁ t₂).hom.toNatTrans.app z = _
  rw [Second.composite_hom_app]
  exact Category.comp_id _

open Factorization.Endpoint.Indexed in
/-- The last-factor compositor after lifting through the middle module. -/
def lastLiftComp : lastMap M t₃ ⟶ lastMap M t₁ ≫ lastMap M t₂ :=
  lastMapCell M p ≫ (reindexIso (Middle.transpose M) (Parametric.varyComp t₁ t₂)).hom

theorem lastLiftComp_app (a : LocallyDiscrete Bᵒᵖ) (z : (rightInner M Y₀).obj a) :
    ((lastLiftComp p M).as.app a).toNatTrans.app z =
      (tensorLastComp p ((Middle.transpose M).obj a)).app z := rfl

theorem middleComposite_mapComp_eq_lastLift
    (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}))
    {a b c : LocallyDiscrete B} (f : a ⟶ b) (g : b ⟶ c) :
    ((middleComposite M N).mapComp f g).hom = lastLiftComp (N.mapComp f g).hom M := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro i
  change (_ ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

theorem lastAssociator_composition :
    RespectsEndpointComposition (eqToIso (last_naturality X M t₁))
      (eqToIso (last_naturality X M t₂)) (eqToIso (last_naturality X M t₃))
      (tensorLastComp p (leftInner X M)) (tensorLastComp (lastLiftComp p M) X) := by
  intro z
  change (eqToHom (last_naturality X M t₃)).app z ≫ _ =
    _ ≫ (eqToHom (last_naturality X M t₂)).app _ ≫
      (mapSecond (F := X) (lastMap M t₂)).map ((eqToHom (last_naturality X M t₁)).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rw [tensorLastComp_app, tensorLastComp_app, last_cell_app]
  rw [Second.cell_app, Second.cell_app]
  congr 2
  rw [lastLiftComp_app, tensorLastComp_app]
  rfl

theorem factorOrder_last_composition {X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (s : X ⟶ X') :
    RespectsEndpointComposition (eqToIso (factor_order s t₁).symm)
      (eqToIso (factor_order s t₂).symm) (eqToIso (factor_order s t₃).symm)
      (tensorLastComp p X) (tensorLastComp p X') := by
  intro z
  change (eqToHom (factor_order s t₃).symm).app z ≫ _ =
    _ ≫ (eqToHom (factor_order s t₂).symm).app _ ≫
      (mapSecond (F := X') t₂).map ((eqToHom (factor_order s t₁).symm).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rw [tensorLastComp_app, tensorLastComp_app, Second.cell_app, Second.cell_app, First.on_native, Functor.map_id]
  rfl

theorem identifyFirst_last_composition {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (h : F = F') :
    RespectsEndpointComposition (eqToIso (identifyFirst_last t₁ h))
      (eqToIso (identifyFirst_last t₂ h)) (eqToIso (identifyFirst_last t₃ h))
      (tensorLastComp p F) (tensorLastComp p F') := by
  subst F'
  intro z
  change (eqToHom (identifyFirst_last t₃ rfl)).app z ≫ _ =
    _ ≫ (eqToHom (identifyFirst_last t₂ rfl)).app _ ≫
      (mapSecond (F := F) t₂).map ((eqToHom (identifyFirst_last t₁ rfl)).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

theorem exposeMiddleOutput_composition
    (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN})) :
    RespectsEndpointComposition (exposeMiddleOutput X M N t₁) (exposeMiddleOutput X M N t₂)
      (exposeMiddleOutput X M N t₃)
      (tensorLastComp (lastLiftComp p N) (leftInner X M))
      (tensorLastComp p (leftInner X (middleComposite M N))) :=
  pasteEndpointComposition
    (reverseEndpointComposition (associator (leftInner X M) N Y₀) (associator (leftInner X M) N Y₁)
      (associator (leftInner X M) N Y₂) (lastAssociator_composition p (leftInner X M) N))
    (factorOrder_last_composition p (leftInner (leftInner X M) N) (outerAssociator X M N))

theorem crossMiddleOutput_composition
    (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
    (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointComposition (crossMiddleOutput X M N t₁ s) (crossMiddleOutput X M N t₂ s)
      (crossMiddleOutput X M N t₃ s)
      (tensorLastComp (lastLiftComp p M) (leftInner X N))
      (tensorLastComp (lastLiftComp p N) (leftInner X M)) :=
  pasteEndpointComposition (exposeMiddleOutput_composition p X N M)
    (pasteEndpointComposition (factorOrder_last_composition p (leftInner X (middleComposite N M)) (liftCrossing X M N s))
      (reverseEndpointComposition (exposeMiddle X M N Y₀) (exposeMiddle X M N Y₁)
        (exposeMiddle X M N Y₂) (exposeMiddleOutput_composition p X M N)))

end TensorComposition

section ContractionComposition
universe v u vY uY vX uX
variable {B : Type u} [Category.{v} B]
variable {F X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable (r : F ⟶ X)
variable {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})}
variable (n : P ⟶ Q)
variable {b c d : LocallyDiscrete B} (f : b ⟶ c) (g : c ⟶ d)

private def coord {W Z : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} {h k : W ⟶ Z}
    (e : h ⟶ k) (i : B) (y : W.obj ⟨op i⟩) := (e.as.app ⟨op i⟩).toNatTrans.app y

set_option maxHeartbeats 400000 in
private theorem covariantNaturalityCompAt (i : B) (y : (P.obj b).obj ⟨op i⟩) :
    coord (n.naturality (f ≫ g)).hom i y ≫ coord (Q.mapComp f g).hom i ((Second.part (n.app b) i).obj y) =
    (Second.part (n.app d) i).map (coord (P.mapComp f g).hom i y) ≫
      coord (n.naturality g).hom i ((Second.part (P.map f) i).obj y) ≫
        (Second.part (Q.map g) i).map (coord (n.naturality f).hom i y) := by
  have h := congrArg (fun e => coord e i y) (n.naturality_comp f g)
  change coord (n.naturality (f ≫ g)).hom i y ≫
      coord (Q.mapComp f g).hom i ((Second.part (n.app b) i).obj y) =
    (Second.part (n.app d) i).map (coord (P.mapComp f g).hom i y) ≫ 𝟙 _ ≫
      coord (n.naturality g).hom i ((Second.part (P.map f) i).obj y) ≫ 𝟙 _ ≫
      (Second.part (Q.map g) i).map (coord (n.naturality f).hom i y) ≫ 𝟙 _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

set_option maxHeartbeats 500000 in
/-- Both contractions respect composition: at each vertex the second payload
is the original strong naturality equation, with the first payload fixed. -/
theorem contractChangeLast_composition :
    RespectsEndpointComposition
      (contractChangeLast r (P.map f) (Q.map f) (n.app b) (n.app c) (n.naturality f))
      (contractChangeLast r (P.map g) (Q.map g) (n.app c) (n.app d) (n.naturality g))
      (contractChangeLast r (P.map (f ≫ g)) (Q.map (f ≫ g)) (n.app b) (n.app d) (n.naturality (f ≫ g)))
      (tensorLastComp (P.mapComp f g).hom F) (tensorLastComp (Q.mapComp f g).hom X) := by
  intro z
  change (contractChangeLast r (P.map (f ≫ g)) (Q.map (f ≫ g)) (n.app b) (n.app d) (n.naturality (f ≫ g))).hom.app z ≫
    (tensorLastComp (Q.mapComp f g).hom X).app ((mapBoth r (n.app b)).obj z) =
    (mapBoth r (n.app d)).map ((tensorLastComp (P.mapComp f g).hom F).app z) ≫
      (contractChangeLast r (P.map g) (Q.map g) (n.app c) (n.app d) (n.naturality g)).hom.app ((mapSecond (P.map f)).obj z) ≫
        (mapSecond (Q.map g)).map ((contractChangeLast r (P.map f) (Q.map f) (n.app b) (n.app c) (n.naturality f)).hom.app z)
  rw [contractChangeLast_app, contractChangeLast_app, contractChangeLast_app, tensorLastComp_app, tensorLastComp_app,
    Second.cell_app, Second.cell_app, mapBoth_native, Functor.map_id, Second.on_native]
  let J := CategoryTheory.Prod.sectR ((First.part r z.as.mid).obj z.as.first) ((Q.obj d).obj ⟨op z.as.mid⟩) ⋙
    insertion X (Q.obj d) z.as.mid
  change J.map (coord (n.naturality (f ≫ g)).hom z.as.mid z.as.second) ≫
      J.map (coord (Q.mapComp f g).hom z.as.mid ((Second.part (n.app b) z.as.mid).obj z.as.second)) =
    J.map ((Second.part (n.app d) z.as.mid).map (coord (P.mapComp f g).hom z.as.mid z.as.second)) ≫
      J.map (coord (n.naturality g).hom z.as.mid ((Second.part (P.map f) z.as.mid).obj z.as.second)) ≫
        J.map ((Second.part (Q.map g) z.as.mid).map (coord (n.naturality f).hom z.as.mid z.as.second))
  rw [← J.map_comp, ← J.map_comp, ← J.map_comp, covariantNaturalityCompAt]

end ContractionComposition

section MixedComposition
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- The supplied covariant action compositor evaluated in the actual input fibre. -/
def covariantCompAt.{w,k} (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k}))
    (a : B) {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    ((P.map (f ≫ g).toLoc).app ⟨op a⟩).toFunctor ⟶
      ((P.map f.toLoc).app ⟨op a⟩).toFunctor ⋙ ((P.map g.toLoc).app ⟨op a⟩).toFunctor :=
  ((P.mapComp f.toLoc g.toLoc).hom.as.app ⟨op a⟩).toNatTrans

theorem covariantCompAt_composite.{vB,uB,vP,uP,vQ,uQ} {D : Type uB} [Category.{vB} D]
    (P : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vP,uP}))
    (Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vQ,uQ}))
    (a : D) {b c d : D} (f : b ⟶ c) (g : c ⟶ d) :
    covariantCompAt (middleComposite P Q) a f g = tensorLastComp (Q.mapComp f.toLoc g.toLoc).hom (row P a) := by
  unfold covariantCompAt
  rw [middleComposite_mapComp_eq_lastLift P Q f.toLoc g.toLoc]
  rfl

set_option maxHeartbeats 600000 in
theorem mixedContractionOutput_composition
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) (a : B)
    {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    let q := (N.mapComp f.toLoc g.toLoc).hom
    RespectsEndpointComposition (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a f)
      (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a g)
      (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a (f ≫ g))
      (tensorLastComp (lastLiftComp q N) (leftInner (row M a) M)) (tensorLastComp q (row M a)) := by
  dsimp only
  have h := contractChangeLast_composition (rowMultiplication.{v,u,vM,uM} M m a) n f.toLoc g.toLoc
  rw [middleComposite_mapComp_eq_lastLift N N f.toLoc g.toLoc] at h
  exact h

set_option maxHeartbeats 800000 in
/-- The original mixed multiplication respects the chosen output-action compositors
of H⊙H and H (H = M⊙N), on the actual retained quotient at fixed input. -/
theorem mixedMultiplicationOutput_composition
    (s : middleComposite N M ⟶ middleComposite M N) (m : middleComposite M M ⟶ M)
    (n : middleComposite N N ⟶ N) (a : B) {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    let H := middleComposite M N
    let HH := middleComposite H H
    let σ₁ := mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a f
    let σ₂ := mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a g
    let σ₃ := mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a (f ≫ g)
    RespectsEndpointComposition σ₁ σ₂ σ₃ (covariantCompAt HH a f g) (covariantCompAt H a f g) := by
  dsimp only
  let H := middleComposite M N
  let p := (N.mapComp f.toLoc g.toLoc).hom
  have hq : (H.mapComp f.toLoc g.toLoc).hom = lastLiftComp p M :=
    middleComposite_mapComp_eq_lastLift M N f.toLoc g.toLoc
  rw [covariantCompAt_composite H H a f g, covariantCompAt_composite M N a f g, hq]
  exact pasteEndpointComposition (identifyFirst_last_composition (lastLiftComp p M) (middleRow M N a))
    (pasteEndpointComposition (crossMiddleOutput_composition p (row M a) M N s)
      (mixedContractionOutput_composition M N m n a f g))

end MixedComposition
end ContextualComposition.RelativeTensor.Iterated
