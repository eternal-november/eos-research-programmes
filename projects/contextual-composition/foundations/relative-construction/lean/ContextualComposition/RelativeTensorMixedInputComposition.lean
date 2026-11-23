module
public import ContextualComposition.RelativeTensorMixedInputIdentity
public import ContextualComposition.RelativeTensorMixedOutputComposition

@[expose] public section
open CategoryTheory
open scoped CategoryTheory.Bicategory

namespace ContextualComposition.RelativeTensor.Iterated.BicategoricalPasting
open CategoryTheory.Bicategory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private def PasteLaw {K : Type*} [Bicategory K]
    {A₀ A₁ A₂ B₀ B₁ B₂ : K}
    {u₁ : A₀ ⟶ A₁} {u₂ : A₁ ⟶ A₂} {u₃ : A₀ ⟶ A₂}
    {v₁ : B₀ ⟶ B₁} {v₂ : B₁ ⟶ B₂} {v₃ : B₀ ⟶ B₂}
    {r₀ : A₀ ⟶ B₀} {r₁ : A₁ ⟶ B₁} {r₂ : A₂ ⟶ B₂}
    (s₁ : u₁ ≫ r₁ ⟶ r₀ ≫ v₁) (s₂ : u₂ ≫ r₂ ⟶ r₁ ≫ v₂)
    (s₃ : u₃ ≫ r₂ ⟶ r₀ ≫ v₃)
    (p : u₃ ⟶ u₁ ≫ u₂) (q : v₃ ⟶ v₁ ≫ v₂) : Prop :=
  s₃ ≫ r₀ ◁ q =
    p ▷ r₂ ≫ (α_ u₁ u₂ r₂).hom ≫ u₁ ◁ s₂ ≫ (α_ u₁ r₁ v₂).inv ≫
      s₁ ▷ v₂ ≫ (α_ r₀ v₁ v₂).hom

section
variable {K L : Type*} [Bicategory K] [Bicategory L] (T : K ⥤ᵖ L)
private def square {a b c d : K} {u : a ⟶ b} {r : b ⟶ d} {l : a ⟶ c} {v : c ⟶ d}
    (s : u ≫ r ⟶ l ≫ v) : T.map u ≫ T.map r ⟶ T.map l ≫ T.map v :=
  (T.mapComp u r).inv ≫ T.map₂ s ≫ (T.mapComp l v).hom

private def compCell {a b c : K} {u : a ⟶ b} {v : b ⟶ c} {w : a ⟶ c}
    (s : w ⟶ u ≫ v) : T.map w ⟶ T.map u ≫ T.map v :=
  T.map₂ s ≫ (T.mapComp u v).hom

private lemma mapAssocInv {a b c d : K} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    T.map₂ (α_ f g h).inv =
      (T.mapComp f (g ≫ h)).hom ≫ T.map f ◁ (T.mapComp g h).hom ≫
      (α_ (T.map f) (T.map g) (T.map h)).inv ≫
      (T.mapComp f g).inv ▷ T.map h ≫ (T.mapComp (f ≫ g) h).inv := by
  rw [T.mapComp_assoc_right_hom_assoc]
  simp

set_option maxHeartbeats 100000 in
private theorem liftPasteLaw
    {A₀ A₁ A₂ B₀ B₁ B₂ : K}
    {u₁ : A₀ ⟶ A₁} {u₂ : A₁ ⟶ A₂} {u₃ : A₀ ⟶ A₂}
    {v₁ : B₀ ⟶ B₁} {v₂ : B₁ ⟶ B₂} {v₃ : B₀ ⟶ B₂}
    {r₀ : A₀ ⟶ B₀} {r₁ : A₁ ⟶ B₁} {r₂ : A₂ ⟶ B₂}
    {s₁ : u₁ ≫ r₁ ⟶ r₀ ≫ v₁} {s₂ : u₂ ≫ r₂ ⟶ r₁ ≫ v₂}
    {s₃ : u₃ ≫ r₂ ⟶ r₀ ≫ v₃}
    {p : u₃ ⟶ u₁ ≫ u₂} {q : v₃ ⟶ v₁ ≫ v₂}
    (h : PasteLaw s₁ s₂ s₃ p q) :
    PasteLaw (square T s₁) (square T s₂) (square T s₃) (compCell T p) (compCell T q) := by
  unfold PasteLaw at h ⊢
  have e := congrArg T.map₂ h
  -- Cancel the outer compositors, then normalize the image of each path.
  apply (cancel_epi (T.mapComp u₃ r₂).hom).mp
  apply (cancel_mono (T.map r₀ ◁ (T.mapComp v₁ v₂).inv ≫ (T.mapComp r₀ (v₁ ≫ v₂)).inv)).mp
  simp only [PrelaxFunctor.map₂_comp, T.map₂_whisker_left, T.map₂_whisker_right,
    T.map₂_associator, mapAssocInv T, Category.assoc, Iso.inv_hom_id_assoc] at e
  simp only [square, compCell, whiskerLeft_comp, comp_whiskerRight, Category.assoc,
    Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc]
  exact e

end

private theorem catPasteLaw_to_pointwise
    {A₀ A₁ A₂ B₀ B₁ B₂ : Cat}
    {u₁ : A₀ ⟶ A₁} {u₂ : A₁ ⟶ A₂} {u₃ : A₀ ⟶ A₂}
    {v₁ : B₀ ⟶ B₁} {v₂ : B₁ ⟶ B₂} {v₃ : B₀ ⟶ B₂}
    {r₀ : A₀ ⟶ B₀} {r₁ : A₁ ⟶ B₁} {r₂ : A₂ ⟶ B₂}
    {s₁ : u₁.toFunctor ⋙ r₁.toFunctor ≅ r₀.toFunctor ⋙ v₁.toFunctor}
    {s₂ : u₂.toFunctor ⋙ r₂.toFunctor ≅ r₁.toFunctor ⋙ v₂.toFunctor}
    {s₃ : u₃.toFunctor ⋙ r₂.toFunctor ≅ r₀.toFunctor ⋙ v₃.toFunctor}
    {p : u₃.toFunctor ⟶ u₁.toFunctor ⋙ u₂.toFunctor}
    {q : v₃.toFunctor ⟶ v₁.toFunctor ⋙ v₂.toFunctor}
    (h : PasteLaw s₁.hom.toCatHom₂ s₂.hom.toCatHom₂ s₃.hom.toCatHom₂ p.toCatHom₂ q.toCatHom₂) :
    ContextualComposition.RelativeTensor.Iterated.RespectsEndpointComposition s₁ s₂ s₃ p q := by
  intro z
  have hz := congrArg (fun m => m.toNatTrans.app z) h
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl, Category.id_comp, Category.comp_id] at hz
  exact hz

end ContextualComposition.RelativeTensor.Iterated.BicategoricalPasting

namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section FirstComp
universe v u vX uX vM uM vN uN vY uY
variable {B : Type u} [Category.{v} B]
variable {X₀ X₁ X₂ : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable {t₁ : X₀ ⟶ X₁} {t₂ : X₁ ⟶ X₂} {t₃ : X₀ ⟶ X₂}
variable (p : t₃ ⟶ t₁ ≫ t₂)
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

def tensorFirstComp : mapFirst (G := Y) t₃ ⟶ mapFirst (G := Y) t₁ ⋙ mapFirst (G := Y) t₂ :=
  First.mapCell (G := Y) p.as ≫ (First.compositeIso Y t₁ t₂).hom.toNatTrans

theorem tensorFirstComp_app (z : Tensor X₀ Y) :
    (tensorFirstComp p Y).app z = (First.mapCell (G := Y) p.as).app z := by
  change _ ≫ (First.compositeIso Y t₁ t₂).hom.toNatTrans.app z = _
  rw [First.composite_hom_app]
  exact Category.comp_id _

private theorem firstMap_naturality_hom (t : X₀ ⟶ X₁)
    {a b : LocallyDiscrete B} (f : a ⟶ b) (z : Tensor X₀ (M.obj a)) :
    ((firstMap t M).naturality f).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (factor_order t (M.map f)).symm).app z = _
  rw [eqToHom_app]; rfl

set_option maxHeartbeats 350000 in
def firstMapCompIso : firstMap (t₁ ≫ t₂) M ≅ firstMap t₁ M ≫ firstMap t₂ M :=
  Pseudofunctor.StrongTrans.isoMk (fun j => First.compositeIso (M.obj j) t₁ t₂) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (First.compositeIso (M.obj b) t₁ t₂).hom.toNatTrans.app _ ≫
      (𝟙 _ ≫ (mapFirst (G := M.obj b) t₂).map (((firstMap t₁ M).naturality f).hom.toNatTrans.app z) ≫
        𝟙 _ ≫ ((firstMap t₂ M).naturality f).hom.toNatTrans.app ((mapFirst (G := M.obj a) t₁).obj z) ≫ 𝟙 _) =
      ((firstMap (t₁ ≫ t₂) M).naturality f).hom.toNatTrans.app z ≫
        (mapSecond (F := X₂) (M.map f)).map ((First.compositeIso (M.obj a) t₁ t₂).hom.toNatTrans.app z)
    rw [First.composite_hom_app, First.composite_hom_app, firstMap_naturality_hom, firstMap_naturality_hom,
      firstMap_naturality_hom]
    erw [Functor.map_id]
    change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp])

def firstLiftComp : firstMap t₃ M ⟶ firstMap t₁ M ≫ firstMap t₂ M :=
  firstMapCell p M ≫ (firstMapCompIso M).hom

theorem firstLiftComp_app (j : LocallyDiscrete B) (z : Tensor X₀ (M.obj j)) :
    ((firstLiftComp p M).as.app j).toNatTrans.app z = (tensorFirstComp p (M.obj j)).app z := rfl

private theorem associate_liftedFirstComp :
    ∀ z : Left X₀ M Y,
    (tensorFirstComp p (rightInner M Y)).app ((associate X₀ M Y).obj z) =
      (associate X₂ M Y).map ((tensorFirstComp (firstLiftComp p M) Y).app z) := by
  intro z
  rw [tensorFirstComp_app, tensorFirstComp_app]
  have h := first_cell_app p M Y z
  rw [First.cell_app] at h ⊢
  refine h.symm.trans ?_
  congr 2
  rw [firstLiftComp_app, tensorFirstComp_app]
  rfl

theorem firstAssociator_composition :
    RespectsEndpointComposition (eqToIso (first_naturality t₁ M Y)) (eqToIso (first_naturality t₂ M Y))
      (eqToIso (first_naturality t₃ M Y))
      (tensorFirstComp (firstLiftComp p M) Y) (tensorFirstComp p (rightInner M Y)) := by
  intro z
  change (eqToHom (first_naturality t₃ M Y)).app z ≫ _ =
    _ ≫ (eqToHom (first_naturality t₂ M Y)).app _ ≫
      (mapFirst (G := rightInner M Y) t₂).map ((eqToHom (first_naturality t₁ M Y)).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  exact (Category.id_comp _).trans (associate_liftedFirstComp p M Y z)


variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))

set_option maxHeartbeats 100000 in
private theorem nativeColumnComp (i : B) (x : Left X₀ M (N.obj ⟨i⟩)) :
    ((firstLiftComp p (middleComposite M N)).as.app ⟨i⟩).toNatTrans.app
        ((associate X₀ M (N.obj ⟨i⟩)).obj x) =
      (associate X₂ M (N.obj ⟨i⟩)).map
        (((firstLiftComp (firstLiftComp p M) N).as.app ⟨i⟩).toNatTrans.app x) := by
  rw [firstLiftComp_app, firstLiftComp_app]
  exact associate_liftedFirstComp p M (N.obj ⟨i⟩) x

open BicategoricalPasting

set_option maxHeartbeats 200000 in
private theorem outerAssociatorPasteLaw :
    PasteLaw (outerAssociatorInput t₁ M N).hom (outerAssociatorInput t₂ M N).hom
      (outerAssociatorInput t₃ M N).hom (firstLiftComp (firstLiftComp p M) N)
      (firstLiftComp p (middleComposite M N)) := by
  unfold PasteLaw
  apply Pseudofunctor.StrongTrans.homCategory.ext; intro d
  apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
  change ((outerAssociatorInput t₃ M N).hom.as.app d).toNatTrans.app x ≫
    ((firstLiftComp p (middleComposite M N)).as.app d).toNatTrans.app
      ((associate X₀ M (N.obj d)).obj x) =
    (associate X₂ M (N.obj d)).map (((firstLiftComp (firstLiftComp p M) N).as.app d).toNatTrans.app x) ≫
      𝟙 _ ≫ ((outerAssociatorInput t₂ M N).hom.as.app d).toNatTrans.app
        ((First.part (firstMap (firstMap t₁ M) N) d.as).obj x) ≫
        𝟙 _ ≫ (First.part (firstMap t₂ (middleComposite M N)) d.as).map
          (((outerAssociatorInput t₁ M N).hom.as.app d).toNatTrans.app x) ≫ 𝟙 _
  rw [outerAssociatorInput_app, outerAssociatorInput_app, outerAssociatorInput_app]
  erw [Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  change _ = _ ≫ (𝟙 _ ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]
  exact nativeColumnComp p M N d.as x

set_option maxHeartbeats 100000 in
private theorem outerAssociatorPasteLaw_mapped :
    PasteLaw (square (First.action Y) (outerAssociatorInput t₁ M N).hom)
      (square (First.action Y) (outerAssociatorInput t₂ M N).hom)
      (square (First.action Y) (outerAssociatorInput t₃ M N).hom)
      (compCell (First.action Y) (firstLiftComp (firstLiftComp p M) N))
      (compCell (First.action Y) (firstLiftComp p (middleComposite M N))) :=
  liftPasteLaw (First.action Y) (outerAssociatorPasteLaw p M N)

set_option maxHeartbeats 100000 in
private theorem actualSquare_hom_bridge (t : X₀ ⟶ X₁) :
    square (First.action Y) (outerAssociatorInput t M N).hom =
      (firstPentagonInput t M N Y).hom.toCatHom₂ := rfl

set_option maxHeartbeats 100000 in
private theorem actualCompCell_bridge.{vF,uF} {F₀ F₁ F₂ : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}}
    {u₁ : F₀ ⟶ F₁} {u₂ : F₁ ⟶ F₂} {u₃ : F₀ ⟶ F₂} (a : u₃ ⟶ u₁ ≫ u₂) :
    compCell (First.action Y) a = (tensorFirstComp a Y).toCatHom₂ := rfl

set_option maxHeartbeats 100000 in
theorem firstPentagonInput_composition :
    RespectsEndpointComposition (firstPentagonInput t₁ M N Y) (firstPentagonInput t₂ M N Y)
      (firstPentagonInput t₃ M N Y)
      (tensorFirstComp (firstLiftComp (firstLiftComp p M) N) Y)
      (tensorFirstComp (firstLiftComp p (middleComposite M N)) Y) := by
  have hm := outerAssociatorPasteLaw_mapped p M Y N
  rw [actualSquare_hom_bridge, actualSquare_hom_bridge, actualSquare_hom_bridge,
    actualCompCell_bridge, actualCompCell_bridge] at hm
  exact catPasteLaw_to_pointwise
    (u₁ := (First.action Y).map (firstMap (firstMap t₁ M) N))
    (u₂ := (First.action Y).map (firstMap (firstMap t₂ M) N))
    (u₃ := (First.action Y).map (firstMap (firstMap t₃ M) N))
    (v₁ := (First.action Y).map (firstMap t₁ (middleComposite M N)))
    (v₂ := (First.action Y).map (firstMap t₂ (middleComposite M N)))
    (v₃ := (First.action Y).map (firstMap t₃ (middleComposite M N)))
    (r₀ := (First.action Y).map (outerAssociator X₀ M N))
    (r₁ := (First.action Y).map (outerAssociator X₁ M N))
    (r₂ := (First.action Y).map (outerAssociator X₂ M N))
    (s₁ := firstPentagonInput t₁ M N Y) (s₂ := firstPentagonInput t₂ M N Y)
    (s₃ := firstPentagonInput t₃ M N Y)
    (p := tensorFirstComp (firstLiftComp (firstLiftComp p M) N) Y)
    (q := tensorFirstComp (firstLiftComp p (middleComposite M N)) Y)
    hm


theorem exposeMiddleInput_composition :
    RespectsEndpointComposition (exposeMiddleInput t₁ M N Y) (exposeMiddleInput t₂ M N Y)
      (exposeMiddleInput t₃ M N Y)
      (tensorFirstComp (firstLiftComp p M) (rightInner N Y))
      (tensorFirstComp (firstLiftComp p (middleComposite M N)) Y) :=
  pasteEndpointComposition
    (reverseEndpointComposition (associator (leftInner X₀ M) N Y) (associator (leftInner X₁ M) N Y)
      (associator (leftInner X₂ M) N Y) (firstAssociator_composition (firstLiftComp p M) N Y))
    (firstPentagonInput_composition p M Y N)

set_option maxHeartbeats 450000 in
private theorem crossingPayload_first_comp.{vP,uP}
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vP,uP})} (s : P ⟶ Q)
    (z : Tensor (leftInner X₀ P) Y) :
    (tensorFirstComp (firstLiftComp p Q) Y).app
        ((mapFirst (G := Y) (crossingPayload X₀ s)).obj z) =
      (mapFirst (G := Y) (crossingPayload X₂ s)).map ((tensorFirstComp (firstLiftComp p P) Y).app z) := by
  rw [tensorFirstComp_app, tensorFirstComp_app, First.cell_app, First.cell_app, First.on_native]
  congr 2
  rw [firstLiftComp_app, firstLiftComp_app, tensorFirstComp_app, tensorFirstComp_app, First.cell_app, First.cell_app]
  let j := z.as.first.as.mid
  let x := z.as.first.as.first
  let y := z.as.first.as.second
  have hx := Second.on_native (F := X₂) (s.app ⟨z.as.mid⟩)
    ((p.as.app ⟨j⟩).toNatTrans.app x) (𝟙 y)
  rw [Functor.map_id] at hx
  exact hx.symm

set_option maxHeartbeats 450000 in
private theorem crossingPayload_first_comp_coherence.{vP,uP}
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vP,uP})} (s : P ⟶ Q)
    (e₁ : mapFirst (G := Y) (firstMap t₁ P) ⋙ mapFirst (crossingPayload X₁ s) =
      mapFirst (G := Y) (crossingPayload X₀ s) ⋙ mapFirst (firstMap t₁ Q))
    (e₂ : mapFirst (G := Y) (firstMap t₂ P) ⋙ mapFirst (crossingPayload X₂ s) =
      mapFirst (G := Y) (crossingPayload X₁ s) ⋙ mapFirst (firstMap t₂ Q))
    (e₃ : mapFirst (G := Y) (firstMap t₃ P) ⋙ mapFirst (crossingPayload X₂ s) =
      mapFirst (G := Y) (crossingPayload X₀ s) ⋙ mapFirst (firstMap t₃ Q)) :
    RespectsEndpointComposition (eqToIso e₁) (eqToIso e₂) (eqToIso e₃)
      (tensorFirstComp (firstLiftComp p P) Y) (tensorFirstComp (firstLiftComp p Q) Y) := by
  intro z
  change (eqToHom e₃).app z ≫ _ = _ ≫ (eqToHom e₂).app _ ≫
    (mapFirst (G := Y) (firstMap t₂ Q)).map ((eqToHom e₁).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  exact (Category.id_comp _).trans (crossingPayload_first_comp p Y s z)

theorem exposedCrossing_input_composition (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointComposition (eqToIso (exposedCrossing_input t₁ M N Y s))
      (eqToIso (exposedCrossing_input t₂ M N Y s)) (eqToIso (exposedCrossing_input t₃ M N Y s))
      (tensorFirstComp (firstLiftComp p (middleComposite N M)) Y)
      (tensorFirstComp (firstLiftComp p (middleComposite M N)) Y) :=
  crossingPayload_first_comp_coherence p Y s (exposedCrossing_input t₁ M N Y s)
    (exposedCrossing_input t₂ M N Y s) (exposedCrossing_input t₃ M N Y s)

theorem crossMiddleInput_composition (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointComposition (crossMiddleInput t₁ M N Y s) (crossMiddleInput t₂ M N Y s)
      (crossMiddleInput t₃ M N Y s)
      (tensorFirstComp (firstLiftComp p N) (rightInner M Y))
      (tensorFirstComp (firstLiftComp p M) (rightInner N Y)) :=
  pasteEndpointComposition (exposeMiddleInput_composition p N Y M)
    (pasteEndpointComposition (exposedCrossing_input_composition p M Y N s)
      (reverseEndpointComposition (exposeMiddle X₀ M N Y) (exposeMiddle X₁ M N Y)
        (exposeMiddle X₂ M N Y) (exposeMiddleInput_composition p M Y N)))

end FirstComp

section RowComp
universe v u vM uM vN uN vY uY
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem modification_comp_heq {K L : Type*} [Bicategory K] [Bicategory L]
    {P₀ P₁ P₂ P₀' P₁' P₂' : K ⥤ᵖ L}
    (h₀ : P₀ = P₀') (h₁ : P₁ = P₁') (h₂ : P₂ = P₂')
    {t₁ : P₀ ⟶ P₁} {t₂ : P₁ ⟶ P₂} {t₃ : P₀ ⟶ P₂}
    {t₁' : P₀' ⟶ P₁'} {t₂' : P₁' ⟶ P₂'} {t₃' : P₀' ⟶ P₂'}
    (e₁ : HEq t₁ t₁') (e₂ : HEq t₂ t₂') (e₃ : HEq t₃ t₃')
    (p : t₃ ⟶ t₁ ≫ t₂) (q : t₃' ⟶ t₁' ≫ t₂')
    (h : HEq p.as.app q.as.app) : HEq p q := by
  subst P₀'; subst P₁'; subst P₂'
  cases eq_of_heq e₁; cases eq_of_heq e₂; cases eq_of_heq e₃
  apply heq_of_eq
  apply Pseudofunctor.StrongTrans.homCategory.ext
  exact congrFun (eq_of_heq h)

set_option maxHeartbeats 450000 in
theorem middleRow_changeComp {a b c : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    HEq (Middle.changeComposition (middleComposite M N) f g).hom
      (firstLiftComp (Middle.changeComposition M f g).hom N) := by
  apply modification_comp_heq (middleRow M N a.as.unop) (middleRow M N b.as.unop) (middleRow M N c.as.unop)
    (middleRow_change M N f) (middleRow_change M N g) (middleRow_change M N (f ≫ g))
  apply heq_of_eq
  funext j
  apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
  change (((middleComposite M N).obj j).mapComp f g).hom.toNatTrans.app z = _
  rw [OuterRow.columnComp M N f g j.as, firstLiftComp_app, tensorFirstComp_app]

private theorem identifyFirst_first_composition
    {F₀ F₁ F₂ F₀' F₁' F₂' : LocallyDiscrete B ⥤ᵖ Cat.{vM,uM}}
    (h₀ : F₀ = F₀') (h₁ : F₁ = F₁') (h₂ : F₂ = F₂')
    {t₁ : F₀ ⟶ F₁} {t₂ : F₁ ⟶ F₂} {t₃ : F₀ ⟶ F₂}
    {t₁' : F₀' ⟶ F₁'} {t₂' : F₁' ⟶ F₂'} {t₃' : F₀' ⟶ F₂'}
    (e₁ : HEq t₁ t₁') (e₂ : HEq t₂ t₂') (e₃ : HEq t₃ t₃')
    (p : t₃ ⟶ t₁ ≫ t₂) (q : t₃' ⟶ t₁' ≫ t₂') (hp : HEq p q)
    (he₁ : mapFirst (G := Y) t₁ ⋙ (identifyFirst h₁ Y).functor =
      (identifyFirst h₀ Y).functor ⋙ mapFirst (G := Y) t₁')
    (he₂ : mapFirst (G := Y) t₂ ⋙ (identifyFirst h₂ Y).functor =
      (identifyFirst h₁ Y).functor ⋙ mapFirst (G := Y) t₂')
    (he₃ : mapFirst (G := Y) t₃ ⋙ (identifyFirst h₂ Y).functor =
      (identifyFirst h₀ Y).functor ⋙ mapFirst (G := Y) t₃') :
    RespectsEndpointComposition (eqToIso he₁) (eqToIso he₂) (eqToIso he₃)
      (tensorFirstComp p Y) (tensorFirstComp q Y) := by
  subst F₀'; subst F₁'; subst F₂'
  cases eq_of_heq e₁; cases eq_of_heq e₂; cases eq_of_heq e₃
  cases eq_of_heq hp
  intro z
  change (eqToHom he₃).app z ≫ _ = _ ≫ (eqToHom he₂).app _ ≫ (mapFirst (G := Y) t₂).map ((eqToHom he₁).app z)
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  erw [Functor.map_id, Category.comp_id]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

theorem rightRow_change_composition {a b c : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    RespectsEndpointComposition (eqToIso (rightRow_change M N f Y)) (eqToIso (rightRow_change M N g Y))
      (eqToIso (rightRow_change M N (f ≫ g) Y))
      (tensorFirstComp (Middle.changeComposition (middleComposite M N) f g).hom Y)
      (tensorFirstComp (firstLiftComp (Middle.changeComposition M f g).hom N) Y) :=
  identifyFirst_first_composition Y (middleRow M N a.as.unop) (middleRow M N b.as.unop) (middleRow M N c.as.unop)
    (middleRow_change M N f) (middleRow_change M N g) (middleRow_change M N (f ≫ g)) _ _
    (middleRow_changeComp M N f g) (rightRow_change M N f Y) (rightRow_change M N g Y) (rightRow_change M N (f ≫ g) Y)

end RowComp

section Contraction
open CategoryTheory.Bicategory
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]

private def SquareComp {K : Type*} [Bicategory K]
    {A₀ A₁ A₂ D₀ D₁ D₂ : K}
    {u₁ : A₀ ⟶ A₁} {u₂ : A₁ ⟶ A₂} {u₃ : A₀ ⟶ A₂}
    {v₁ : D₀ ⟶ D₁} {v₂ : D₁ ⟶ D₂} {v₃ : D₀ ⟶ D₂}
    {r₀ : A₀ ⟶ D₀} {r₁ : A₁ ⟶ D₁} {r₂ : A₂ ⟶ D₂}
    (σ₁ : u₁ ≫ r₁ ≅ r₀ ≫ v₁) (σ₂ : u₂ ≫ r₂ ≅ r₁ ≫ v₂) (σ₃ : u₃ ≫ r₂ ≅ r₀ ≫ v₃)
    (p : u₃ ⟶ u₁ ≫ u₂) (q : v₃ ⟶ v₁ ≫ v₂) : Prop :=
  σ₃.hom ≫ r₀ ◁ q = p ▷ r₂ ≫ (α_ _ _ _).hom ≫ u₁ ◁ σ₂.hom ≫
    (α_ _ _ _).inv ≫ σ₁.hom ▷ v₂ ≫ (α_ _ _ _).hom

private theorem transportRowSquare_comp {K : Type*} [Bicategory K]
    {A₀ A₁ A₂ A₀' A₁' A₂' D₀ D₁ D₂ : K}
    (h₀ : A₀ = A₀') (h₁ : A₁ = A₁') (h₂ : A₂ = A₂')
    {u₁ : A₀ ⟶ A₁} {u₂ : A₁ ⟶ A₂} {u₃ : A₀ ⟶ A₂}
    {u₁' : A₀' ⟶ A₁'} {u₂' : A₁' ⟶ A₂'} {u₃' : A₀' ⟶ A₂'}
    (e₁ : HEq u₁ u₁') (e₂ : HEq u₂ u₂') (e₃ : HEq u₃ u₃')
    {v₁ : D₀ ⟶ D₁} {v₂ : D₁ ⟶ D₂} {v₃ : D₀ ⟶ D₂}
    (r₀ : A₀ ⟶ D₀) (r₁ : A₁ ⟶ D₁) (r₂ : A₂ ⟶ D₂)
    (σ₁ : u₁ ≫ r₁ ≅ r₀ ≫ v₁) (σ₂ : u₂ ≫ r₂ ≅ r₁ ≫ v₂) (σ₃ : u₃ ≫ r₂ ≅ r₀ ≫ v₃)
    (p : u₃ ⟶ u₁ ≫ u₂) (p' : u₃' ⟶ u₁' ≫ u₂') (hp : HEq p p') (q : v₃ ⟶ v₁ ≫ v₂)
    (h : SquareComp σ₁ σ₂ σ₃ p q) :
    SquareComp (transportRowSquare h₀ h₁ e₁ r₀ r₁ v₁ σ₁)
      (transportRowSquare h₁ h₂ e₂ r₁ r₂ v₂ σ₂) (transportRowSquare h₀ h₂ e₃ r₀ r₂ v₃ σ₃) p' q := by
  subst A₀'; subst A₁'; subst A₂'
  cases eq_of_heq e₁; cases eq_of_heq e₂; cases eq_of_heq e₃
  cases eq_of_heq hp
  exact h

private theorem rowMap_comp
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vX,uX})}
    (s : P ⟶ Q) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    SquareComp (rowMap_changeIso s g) (rowMap_changeIso s f) (rowMap_changeIso s (f ≫ g))
      (Middle.changeComposition P g.op.toLoc f.op.toLoc).hom
      (Middle.changeComposition Q g.op.toLoc f.op.toLoc).hom := by
  unfold SquareComp
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro j
  exact (s.app j).naturality_comp g.op.toLoc f.op.toLoc

variable {F₀ F₁ F₂ X₀ X₁ X₂ : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable {G Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}

theorem contractChange_hom_app {F F' X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    (t : F ⟶ F') (t' : X ⟶ X') (r : F ⟶ X) (r' : F' ⟶ X') (n : G ⟶ Y)
    (e : t ≫ r' ≅ r ≫ t') (z : Tensor F G) :
    (contractChange t t' r r' n e).hom.app z = (insertion X' Y z.as.mid).map
      (productMap ((e.hom.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first)
        (𝟙 ((Second.part n z.as.mid).obj z.as.second))) := by
  unfold contractChange
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.mapIso_hom]
  change (mapSecond (F := X') n).map
    ((eqToHom (First.map_composite (G := G) t r').symm).app z ≫
      (First.mapCell (G := G) e.hom.as).app z ≫ (eqToHom (First.map_composite (G := G) r t')).app z) ≫
    (eqToHom (congrArg (mapFirst (G := G) r ⋙ ·) (factor_order t' n))).app z = _
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  change (mapSecond (F := X') n).map
    (𝟙 _ ≫ (First.mapCell (G := G) e.hom.as).app z ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id, First.cell_app, Second.on_native, Functor.map_id]

set_option maxHeartbeats 550000 in
private theorem contractChange_composition
    {t₁ : F₀ ⟶ F₁} {t₂ : F₁ ⟶ F₂} {t₃ : F₀ ⟶ F₂}
    {u₁ : X₀ ⟶ X₁} {u₂ : X₁ ⟶ X₂} {u₃ : X₀ ⟶ X₂}
    (r₀ : F₀ ⟶ X₀) (r₁ : F₁ ⟶ X₁) (r₂ : F₂ ⟶ X₂) (n : G ⟶ Y)
    (e₁ : t₁ ≫ r₁ ≅ r₀ ≫ u₁) (e₂ : t₂ ≫ r₂ ≅ r₁ ≫ u₂) (e₃ : t₃ ≫ r₂ ≅ r₀ ≫ u₃)
    (p : t₃ ⟶ t₁ ≫ t₂) (q : u₃ ⟶ u₁ ≫ u₂) (h : SquareComp e₁ e₂ e₃ p q) :
    RespectsEndpointComposition (contractChange t₁ u₁ r₀ r₁ n e₁) (contractChange t₂ u₂ r₁ r₂ n e₂)
      (contractChange t₃ u₃ r₀ r₂ n e₃) (tensorFirstComp p G) (tensorFirstComp q Y) := by
  intro z
  change (contractChange t₃ u₃ r₀ r₂ n e₃).hom.app z ≫ (tensorFirstComp q Y).app ((mapBoth r₀ n).obj z) =
    (mapBoth r₂ n).map ((tensorFirstComp p G).app z) ≫
      (contractChange t₂ u₂ r₁ r₂ n e₂).hom.app ((mapFirst (G := G) t₁).obj z) ≫
      (mapFirst (G := Y) u₂).map ((contractChange t₁ u₁ r₀ r₁ n e₁).hom.app z)
  rw [contractChange_hom_app, contractChange_hom_app, contractChange_hom_app, tensorFirstComp_app, tensorFirstComp_app,
    First.cell_app, First.cell_app, mapBoth_native, Functor.map_id, First.on_native]
  let j := z.as.mid
  let x := z.as.first
  let J := CategoryTheory.Prod.sectL (X₂.obj ⟨j⟩) ((Second.part n j).obj z.as.second) ⋙ insertion X₂ Y j
  have hh := congrArg (fun e => (e.as.app ⟨j⟩).toNatTrans.app x) h
  change (e₃.hom.as.app ⟨j⟩).toNatTrans.app x ≫
      (q.as.app ⟨j⟩).toNatTrans.app ((First.part r₀ j).obj x) =
    (First.part r₂ j).map ((p.as.app ⟨j⟩).toNatTrans.app x) ≫ 𝟙 _ ≫
      (e₂.hom.as.app ⟨j⟩).toNatTrans.app ((First.part t₁ j).obj x) ≫ 𝟙 _ ≫
      (First.part u₂ j).map ((e₁.hom.as.app ⟨j⟩).toNatTrans.app x) ≫ 𝟙 _ at hh
  simp only [Category.comp_id, Category.id_comp] at hh
  have hh' := congrArg J.map hh
  simp only [Functor.map_comp] at hh'
  exact hh'

end Contraction

section MixedComp
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- The chosen contravariant compositor at fixed output: the transition along
`g` is taken before the transition along `f`. -/
def contravariantCompAt.{w,k} (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k}))
    (d : B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    backward (column P d) (f ≫ g) ⟶ backward (column P d) g ⋙ backward (column P d) f :=
  ((column P d).mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans

theorem contravariantCompAt_composite.{vB,uB,vP,uP,vQ,uQ} {D : Type uB} [Category.{vB} D]
    (P : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vP,uP}))
    (Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vQ,uQ})) (d : D)
    {a b c : D} (f : a ⟶ b) (g : b ⟶ c) :
    contravariantCompAt (middleComposite P Q) d f g =
      tensorFirstComp (Middle.changeComposition P g.op.toLoc f.op.toLoc).hom (column Q d) := rfl

set_option maxHeartbeats 600000 in
theorem mixedContractionInput_composition
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    RespectsEndpointComposition (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n g d)
      (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n f d)
      (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n (f ≫ g) d)
      (tensorFirstComp (firstLiftComp (Middle.changeComposition M g.op.toLoc f.op.toLoc).hom M)
        (rightInner N (column N d)))
      (tensorFirstComp (Middle.changeComposition M g.op.toLoc f.op.toLoc).hom (column N d)) := by
  apply contractChange_composition
  exact transportRowSquare_comp (middleRow M M c) (middleRow M M b) (middleRow M M a)
    (middleRow_change M M g.op.toLoc) (middleRow_change M M f.op.toLoc) (middleRow_change M M (f ≫ g).op.toLoc)
    (rowMap m c) (rowMap m b) (rowMap m a) (rowMap_changeIso m g) (rowMap_changeIso m f) (rowMap_changeIso m (f ≫ g))
    (Middle.changeComposition (middleComposite M M) g.op.toLoc f.op.toLoc).hom
    (firstLiftComp (Middle.changeComposition M g.op.toLoc f.op.toLoc).hom M)
    (middleRow_changeComp M M g.op.toLoc f.op.toLoc) (Middle.changeComposition M g.op.toLoc f.op.toLoc).hom
    (rowMap_comp m f g)

set_option maxHeartbeats 750000 in
/-- The original mixed multiplication respects the chosen contravariant action
compositors of H⊙H and H on the genuine retained quotient at fixed output. -/
theorem mixedMultiplicationInput_composition
    (s : middleComposite N M ⟶ middleComposite M N) (m : middleComposite M M ⟶ M)
    (n : middleComposite N N ⟶ N) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    let H := middleComposite M N
    let HH := middleComposite H H
    RespectsEndpointComposition (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n g d)
      (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n f d)
      (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n (f ≫ g) d)
      (contravariantCompAt HH d f g) (contravariantCompAt H d f g) := by
  dsimp only
  let H := middleComposite M N
  rw [contravariantCompAt_composite H H d f g, contravariantCompAt_composite M N d f g]
  exact pasteEndpointComposition (rightRow_change_composition M N (column H d) g.op.toLoc f.op.toLoc)
    (pasteEndpointComposition
      (crossMiddleInput_composition (Middle.changeComposition M g.op.toLoc f.op.toLoc).hom M (column N d) N s)
      (mixedContractionInput_composition M N m n f g d))

end MixedComp
end ContextualComposition.RelativeTensor.Iterated
