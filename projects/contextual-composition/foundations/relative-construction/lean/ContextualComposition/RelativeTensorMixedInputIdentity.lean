module
public import ContextualComposition.RelativeTensorMixedOutputIdentity
public import ContextualComposition.RelativeTensorOuterRowNative

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section FirstUnit
universe v u vX uX vM uM vN uN vY uY
variable {B : Type u} [Category.{v} B]
variable {X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} {t : X ⟶ X}
variable (p : t ⟶ 𝟙 X)
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

def tensorFirstUnit : mapFirst (G := Y) t ⟶ 𝟭 (Tensor X Y) :=
  First.mapCell (G := Y) p.as ≫ (First.identityIso Y X).hom.toNatTrans

theorem tensorFirstUnit_app (z : Tensor X Y) :
    (tensorFirstUnit p Y).app z = (First.mapCell (G := Y) p.as).app z := by
  change _ ≫ (First.identityIso Y X).hom.toNatTrans.app z = _
  rw [First.identity_hom_app]
  exact Category.comp_id _

def firstMapIdIso : firstMap (𝟙 X) M ≅ 𝟙 (leftInner X M) :=
  Pseudofunctor.StrongTrans.isoMk (fun j => First.identityIso (M.obj j) X) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (First.identityIso (M.obj b) X).hom.toNatTrans.app _ ≫ (𝟙 _ ≫ 𝟙 _) =
      (Parametric.interchange (𝟙 X) (M.map f)).inv.toNatTrans.app z ≫
        (mapSecond (M.map f)).map ((First.identityIso (M.obj a) X).hom.toNatTrans.app z)
    have hi : (Parametric.interchange (𝟙 X) (M.map f)).inv.toNatTrans.app z = 𝟙 _ := by
      change (eqToHom (factor_order (𝟙 X) (M.map f)).symm).app z = _
      rw [eqToHom_app]; rfl
    rw [First.identity_hom_app, First.identity_hom_app, hi]
    simp only [Category.id_comp]
    exact ((mapSecond (F := X) (M.map f)).map_id z).symm)

def firstLiftUnit : firstMap t M ⟶ 𝟙 (leftInner X M) :=
  firstMapCell p M ≫ (firstMapIdIso M).hom

theorem firstLiftUnit_app (j : LocallyDiscrete B) (z : Tensor X (M.obj j)) :
    ((firstLiftUnit p M).as.app j).toNatTrans.app z = (tensorFirstUnit p (M.obj j)).app z := rfl

theorem firstAssociator_identity :
    RespectsEndpointIdentity (eqToIso (first_naturality t M Y))
      (tensorFirstUnit (firstLiftUnit p M) Y) (tensorFirstUnit p (rightInner M Y)) := by
  intro z
  change (eqToHom (first_naturality t M Y)).app z ≫ _ = _
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp, tensorFirstUnit_app, tensorFirstUnit_app]
  have h := first_cell_app p M Y z
  rw [First.cell_app] at h ⊢
  refine h.symm.trans ?_
  congr 2
  rw [firstLiftUnit_app, tensorFirstUnit_app]
  rfl


variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))

theorem firstPentagonInput_hom_app (z : farLeft X M N Y) :
    (firstPentagonInput t M N Y).hom.app z = 𝟙 _ := by
  unfold firstPentagonInput
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom]
  change (eqToHom (First.map_composite (G := Y) (firstMap (firstMap t M) N) (outerAssociator X M N)).symm).app z ≫
    (First.mapCell (G := Y) (outerAssociatorInput t M N).hom.as).app z ≫
    (eqToHom (First.map_composite (G := Y) (outerAssociator X M N) (firstMap t (middleComposite M N)))).app z = _
  rw [eqToHom_app, eqToHom_app, First.cell_app, outerAssociatorInput_app]
  erw [Functor.map_id]
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.id_comp]

theorem firstPentagonInput_identity :
    RespectsEndpointIdentity (firstPentagonInput t M N Y)
      (tensorFirstUnit (firstLiftUnit (firstLiftUnit p M) N) Y)
      (tensorFirstUnit (firstLiftUnit p (middleComposite M N)) Y) := by
  intro z
  rw [firstPentagonInput_hom_app]
  change 𝟙 _ ≫ _ = (mapFirst (G := Y) (outerAssociator X M N)).map
    ((tensorFirstUnit (firstLiftUnit (firstLiftUnit p M) N) Y).app z)
  rw [Category.id_comp, tensorFirstUnit_app, tensorFirstUnit_app, First.cell_app, First.cell_app, First.on_native]
  congr 2
  rw [firstLiftUnit_app, firstLiftUnit_app, tensorFirstUnit_app, tensorFirstUnit_app]
  rw [First.cell_app]
  refine (first_cell_app p M (N.obj ⟨z.as.mid⟩) z.as.first).symm.trans ?_
  rw [First.cell_app, First.cell_app, firstLiftUnit_app, tensorFirstUnit_app]
  rfl

theorem exposeMiddleInput_identity :
    RespectsEndpointIdentity (exposeMiddleInput t M N Y)
      (tensorFirstUnit (firstLiftUnit p M) (rightInner N Y))
      (tensorFirstUnit (firstLiftUnit p (middleComposite M N)) Y) :=
  pasteEndpointIdentity
    (reverseEndpointIdentity (associator (leftInner X M) N Y) (firstAssociator_identity (firstLiftUnit p M) N Y))
    (firstPentagonInput_identity p M Y N)

set_option maxHeartbeats 450000 in
private theorem crossingPayload_first_unit.{vP,uP}
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vP,uP})} (s : P ⟶ Q)
    (z : Tensor (leftInner X P) Y) :
    (tensorFirstUnit (firstLiftUnit p Q) Y).app
        ((mapFirst (G := Y) (crossingPayload X s)).obj z) =
      (mapFirst (G := Y) (crossingPayload X s)).map ((tensorFirstUnit (firstLiftUnit p P) Y).app z) := by
  rw [tensorFirstUnit_app, tensorFirstUnit_app, First.cell_app, First.cell_app, First.on_native]
  congr 2
  rw [firstLiftUnit_app, firstLiftUnit_app, tensorFirstUnit_app, tensorFirstUnit_app, First.cell_app, First.cell_app]
  let j := z.as.first.as.mid
  let x := z.as.first.as.first
  let y := z.as.first.as.second
  have hx := Second.on_native (F := X) (s.app ⟨z.as.mid⟩)
    ((p.as.app ⟨j⟩).toNatTrans.app x) (𝟙 y)
  rw [Functor.map_id] at hx
  exact hx.symm

set_option maxHeartbeats 400000 in
private theorem crossingPayload_first_unit_coherence.{vP,uP}
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vP,uP})} (s : P ⟶ Q)
    (e : mapFirst (G := Y) (firstMap t P) ⋙ mapFirst (crossingPayload X s) =
      mapFirst (G := Y) (crossingPayload X s) ⋙ mapFirst (firstMap t Q)) :
    RespectsEndpointIdentity (eqToIso e)
      (tensorFirstUnit (firstLiftUnit p P) Y) (tensorFirstUnit (firstLiftUnit p Q) Y) := by
  intro z
  change (eqToHom e).app z ≫ _ = _
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  exact (Category.id_comp _).trans (crossingPayload_first_unit p Y s z)

theorem exposedCrossing_input_identity (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointIdentity (eqToIso (exposedCrossing_input t M N Y s))
      (tensorFirstUnit (firstLiftUnit p (middleComposite N M)) Y)
      (tensorFirstUnit (firstLiftUnit p (middleComposite M N)) Y) :=
  crossingPayload_first_unit_coherence p Y s (exposedCrossing_input t M N Y s)

theorem crossMiddleInput_identity (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointIdentity (crossMiddleInput t M N Y s)
      (tensorFirstUnit (firstLiftUnit p N) (rightInner M Y))
      (tensorFirstUnit (firstLiftUnit p M) (rightInner N Y)) :=
  pasteEndpointIdentity (exposeMiddleInput_identity p N Y M)
    (pasteEndpointIdentity (exposedCrossing_input_identity p M Y N s)
      (reverseEndpointIdentity (exposeMiddle X M N Y) (exposeMiddleInput_identity p M Y N)))

end FirstUnit

section RowIdentity
universe v u vM uM vN uN vY uY
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem modification_heq {K L : Type*} [Bicategory K] [Bicategory L]
    {P P' : K ⥤ᵖ L} (h : P = P') {t : P ⟶ P} {t' : P' ⟶ P'} (ht : HEq t t')
    (p : t ⟶ 𝟙 P) (q : t' ⟶ 𝟙 P')
    (ha : HEq p.as.app q.as.app) : HEq p q := by
  subst P'
  cases eq_of_heq ht
  apply heq_of_eq
  apply Pseudofunctor.StrongTrans.homCategory.ext
  exact congrFun (eq_of_heq ha)

theorem middleRow_changeUnit (a : LocallyDiscrete Bᵒᵖ) :
    HEq (Middle.changeUnit (middleComposite M N) a).hom (firstLiftUnit (Middle.changeUnit M a).hom N) := by
  apply modification_heq (middleRow M N a.as.unop) (middleRow_change M N (𝟙 a))
  apply heq_of_eq
  funext j
  apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
  change (((middleComposite M N).obj j).mapId a).hom.toNatTrans.app z = _
  rw [OuterRow.columnUnit M N a j.as, firstLiftUnit_app, tensorFirstUnit_app]

private theorem identifyFirst_first_identity
    {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vM,uM}} (h : F = F')
    {t : F ⟶ F} {t' : F' ⟶ F'} (ht : HEq t t') (p : t ⟶ 𝟙 F) (q : t' ⟶ 𝟙 F')
    (hp : HEq p q)
    (he : mapFirst (G := Y) t ⋙ (identifyFirst h Y).functor =
      (identifyFirst h Y).functor ⋙ mapFirst (G := Y) t') :
    RespectsEndpointIdentity (eqToIso he) (tensorFirstUnit p Y) (tensorFirstUnit q Y) := by
  subst F'
  cases eq_of_heq ht
  cases eq_of_heq hp
  intro z
  change (eqToHom he).app z ≫ _ = _
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

theorem rightRow_change_identity (a : LocallyDiscrete Bᵒᵖ) :
    RespectsEndpointIdentity (eqToIso (rightRow_change M N (𝟙 a) Y))
      (tensorFirstUnit (Middle.changeUnit (middleComposite M N) a).hom Y)
      (tensorFirstUnit (firstLiftUnit (Middle.changeUnit M a).hom N) Y) :=
  identifyFirst_first_identity Y (middleRow M N a.as.unop) (middleRow_change M N (𝟙 a)) _ _
    (middleRow_changeUnit M N a) (rightRow_change M N (𝟙 a) Y)

end RowIdentity

section Contract
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]

open CategoryTheory.Bicategory in
private theorem transportRowSquare_unit {K : Type*} [Bicategory K]
    {A A' D : K} (h : A = A') {t : A ⟶ A} {t' : A' ⟶ A'} (e : HEq t t')
    (r : A ⟶ D) {u : D ⟶ D} (σ : t ≫ r ≅ r ≫ u)
    (p : t ⟶ 𝟙 A) (p' : t' ⟶ 𝟙 A') (hp : HEq p p') (q : u ⟶ 𝟙 D)
    (hs : σ.hom ≫ r ◁ q = p ▷ r ≫ (λ_ r).hom ≫ (ρ_ r).inv) :
    let r' := Eq.mp (congrArg (fun k => k ⟶ D) h) r
    (transportRowSquare h h e r r u σ).hom ≫ r' ◁ q =
      p' ▷ r' ≫ (λ_ r').hom ≫ (ρ_ r').inv := by
  subst A'
  cases eq_of_heq e
  cases eq_of_heq hp
  exact hs

open CategoryTheory.Bicategory in
private theorem rowMap_unit
    {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vX,uX})}
    (s : P ⟶ Q) (a : B) :
    (rowMap_changeIso s (𝟙 a)).hom ≫ rowMap s a ◁ (Middle.changeUnit Q ⟨op a⟩).hom =
      (Middle.changeUnit P ⟨op a⟩).hom ▷ rowMap s a ≫ (λ_ (rowMap s a)).hom ≫ (ρ_ (rowMap s a)).inv := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro j
  exact (s.app j).naturality_id ⟨op a⟩

variable {F X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable {G Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}

theorem contractChange_app {t : F ⟶ F} {t' : X ⟶ X} (r : F ⟶ X) (n : G ⟶ Y)
    (e : t ≫ r ≅ r ≫ t') (z : Tensor F G) :
    (contractChange t t' r r n e).hom.app z = (insertion X Y z.as.mid).map
      (productMap ((e.hom.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first)
        (𝟙 ((Second.part n z.as.mid).obj z.as.second))) := by
  unfold contractChange
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.mapIso_hom]
  change (mapSecond (F := X) n).map
    ((eqToHom (First.map_composite (G := G) t r).symm).app z ≫
      (First.mapCell (G := G) e.hom.as).app z ≫ (eqToHom (First.map_composite (G := G) r t')).app z) ≫
    (eqToHom (congrArg (mapFirst (G := G) r ⋙ ·) (factor_order t' n))).app z = _
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  change (mapSecond (F := X) n).map
    (𝟙 _ ≫ (First.mapCell (G := G) e.hom.as).app z ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id, First.cell_app, Second.on_native, Functor.map_id]

open CategoryTheory.Bicategory in
theorem contractChange_identity {t : F ⟶ F} {t' : X ⟶ X} (r : F ⟶ X) (n : G ⟶ Y)
    (e : t ≫ r ≅ r ≫ t') (p : t ⟶ 𝟙 F) (q : t' ⟶ 𝟙 X)
    (h : e.hom ≫ r ◁ q = p ▷ r ≫ (λ_ r).hom ≫ (ρ_ r).inv) :
    RespectsEndpointIdentity (contractChange t t' r r n e) (tensorFirstUnit p G) (tensorFirstUnit q Y) := by
  intro z
  rw [contractChange_app, tensorFirstUnit_app, tensorFirstUnit_app, First.cell_app, First.cell_app,
    mapBoth_native, Functor.map_id]
  let J := CategoryTheory.Prod.sectL (X.obj ⟨z.as.mid⟩) ((Second.part n z.as.mid).obj z.as.second) ⋙
    insertion X Y z.as.mid
  have h' := congrArg (fun e => (e.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first) h
  change
    ((e.hom.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first) ≫
      (q.as.app ⟨z.as.mid⟩).toNatTrans.app ((First.part r z.as.mid).obj z.as.first) =
    (First.part r z.as.mid).map ((p.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first) ≫ 𝟙 _ ≫ 𝟙 _ at h'
  simp only [Category.comp_id] at h'
  exact (J.map_comp _ _).symm.trans (congrArg J.map h')

end Contract

section MixedIdentity
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- Evaluate the chosen contravariant action unitor in the actual output fibre. -/
def contravariantUnitAt.{w,k} (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k}))
    (a b : B) : backward (column P b) (𝟙 a) ⟶ 𝟭 ((column P b).obj ⟨op a⟩) :=
  ((column P b).mapId ⟨op a⟩).hom.toNatTrans

theorem contravariantUnitAt_composite.{vB,uB,vP,uP,vQ,uQ} {D : Type uB} [Category.{vB} D]
    (P : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vP,uP}))
    (Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vQ,uQ})) (a b : D) :
    contravariantUnitAt (middleComposite P Q) a b =
      tensorFirstUnit (Middle.changeUnit P ⟨op a⟩).hom (column Q b) := rfl

set_option maxHeartbeats 450000 in
theorem mixedContractionInput_identity
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) (a b : B) :
    RespectsEndpointIdentity (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n (𝟙 a) b)
      (tensorFirstUnit (firstLiftUnit (Middle.changeUnit M ⟨op a⟩).hom M) (rightInner N (column N b)))
      (tensorFirstUnit (Middle.changeUnit M ⟨op a⟩).hom (column N b)) := by
  apply contractChange_identity
  exact transportRowSquare_unit (middleRow M M a) (middleRow_change M M (𝟙 ⟨op a⟩))
    (rowMap m a) (rowMap_changeIso m (𝟙 a)) (Middle.changeUnit (middleComposite M M) ⟨op a⟩).hom
    (firstLiftUnit (Middle.changeUnit M ⟨op a⟩).hom M) (middleRow_changeUnit M M ⟨op a⟩)
    (Middle.changeUnit M ⟨op a⟩).hom (rowMap_unit m a)

set_option maxHeartbeats 750000 in
/-- The original mixed multiplication respects the chosen contravariant action
unitors of H⊙H and H, on the genuine retained quotient at fixed output. -/
theorem mixedMultiplicationInput_identity
    (s : middleComposite N M ⟶ middleComposite M N) (m : middleComposite M M ⟶ M)
    (n : middleComposite N N ⟶ N) (a b : B) :
    let H := middleComposite M N
    let HH := middleComposite H H
    RespectsEndpointIdentity (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n (𝟙 a) b)
      (contravariantUnitAt HH a b) (contravariantUnitAt H a b) := by
  dsimp only
  let H := middleComposite M N
  rw [contravariantUnitAt_composite H H a b, contravariantUnitAt_composite M N a b]
  exact pasteEndpointIdentity (rightRow_change_identity M N (column H b) ⟨op a⟩)
    (pasteEndpointIdentity (crossMiddleInput_identity (Middle.changeUnit M ⟨op a⟩).hom M (column N b) N s)
      (mixedContractionInput_identity M N m n a b))

end MixedIdentity
end ContextualComposition.RelativeTensor.Iterated
