module
public import ContextualComposition.RelativeTensorMixedMultiplicationOutput

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section Square
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
variable {u : A ⥤ A} {v : B ⥤ B} {w : C ⥤ C} {F : A ⥤ B} {G : B ⥤ C}

/-- The unit equation of a comparison square at an identity transition,
using the given, possibly nontrivial, endpoint action unitors. -/
def RespectsEndpointIdentity (σ : u ⋙ F ≅ F ⋙ v) (α : u ⟶ 𝟭 A) (β : v ⟶ 𝟭 B) : Prop :=
  ∀ z, σ.hom.app z ≫ β.app (F.obj z) = F.map (α.app z)

/-- Pasting squares that respect the supplied unitors respects the outer unitors. -/
theorem pasteEndpointIdentity {σ : u ⋙ F ≅ F ⋙ v} {τ : v ⋙ G ≅ G ⋙ w}
    {α : u ⟶ 𝟭 A} {β : v ⟶ 𝟭 B} {γ : w ⟶ 𝟭 C}
    (hs : RespectsEndpointIdentity σ α β) (ht : RespectsEndpointIdentity τ β γ) :
    RespectsEndpointIdentity (pasteInputSquare σ τ) α γ := by
  intro z
  change (G.map (σ.hom.app z) ≫ τ.hom.app (F.obj z)) ≫ γ.app (G.obj (F.obj z)) =
    G.map (F.map (α.app z))
  rw [Category.assoc, ht, ← Functor.map_comp, hs]

/-- Inverting the vertical equivalence by its actual mate preserves the unit equation. -/
theorem reverseEndpointIdentity (E : A ≌ B) {σ : u ⋙ E.functor ≅ E.functor ⋙ v}
    {α : u ⟶ 𝟭 A} {β : v ⟶ 𝟭 B} (h : RespectsEndpointIdentity σ α β) :
    RespectsEndpointIdentity (reverseInputSquare E E σ) β α := by
  intro z
  let L := E.functor
  let R := E.inverse
  have hh : σ.inv.app (R.obj z) ≫ L.map (α.app (R.obj z)) = β.app (L.obj (R.obj z)) := by
    rw [← h (R.obj z)]
    exact Iso.inv_hom_id_assoc (σ.app (R.obj z)) _
  simp only [reverseInputSquare, Iso.compInverseIso, Iso.isoInverseComp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.associator_hom_app, Iso.symm_hom,
    Category.id_comp]
  erw [Category.comp_id]
  change (R.map (v.map (E.counitIso.inv.app z) ≫ σ.inv.app (R.obj z)) ≫
    E.unitIso.inv.app (u.obj (R.obj z))) ≫ α.app (R.obj z) = R.map (β.app z)
  have hu : R.map (L.map (α.app (R.obj z))) ≫ E.unitIso.inv.app (R.obj z) =
      E.unitIso.inv.app (u.obj (R.obj z)) ≫ α.app (R.obj z) :=
    E.unitIso.inv.naturality (α.app (R.obj z))
  rw [Category.assoc, ← hu, ← Category.assoc, ← R.map_comp, Category.assoc (v.map (E.counitIso.inv.app z)), hh]
  change R.map (v.map (E.counitIso.inv.app z) ≫ β.app (L.obj (R.obj z))) ≫ _ = _
  have hv : v.map (E.counitIso.inv.app z) ≫ β.app (L.obj (R.obj z)) =
      β.app z ≫ E.counitIso.inv.app z := β.naturality (E.counitIso.inv.app z)
  rw [hv]
  change R.map (β.app z ≫ E.counitIso.inv.app z) ≫ _ = _
  have ht : R.map (E.counitIso.inv.app z) ≫ E.unitIso.inv.app (R.obj z) = 𝟙 _ :=
    E.inverse_counitInv_comp z
  rw [Functor.map_comp, Category.assoc, ht, Category.comp_id]

end Square


section TensorUnit
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} {t : Y ⟶ Y}
variable (p : t ⟶ 𝟙 Y)
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))

/-- Unit of a tensor's second-factor action, after supplying the unit cell
for the right factor. The existing action supplies its final identity comparison. -/
def tensorLastUnit : mapSecond (F := X) t ⟶ 𝟭 (Tensor X Y) :=
  Second.mapCell (F := X) p.as ≫ (Second.identityIso X Y).hom.toNatTrans

theorem tensorLastUnit_app (z : Tensor X Y) :
    (tensorLastUnit p X).app z = (Second.mapCell (F := X) p.as).app z := by
  change _ ≫ (Second.identityIso X Y).hom.toNatTrans.app z = _
  rw [Second.identity_hom_app]
  exact Category.comp_id _

open Factorization.Endpoint.Indexed in
/-- The actual unit obtained by tensoring the last-factor unit cell down every row. -/
def lastLiftUnit : lastMap M t ⟶ 𝟙 (rightInner M Y) :=
  lastMapCell M p ≫ (reindexIso (Middle.transpose M) (Parametric.varyId Y)).hom

theorem lastLiftUnit_app (a : LocallyDiscrete Bᵒᵖ) (z : (rightInner M Y).obj a) :
    ((lastLiftUnit p M).as.app a).toNatTrans.app z =
      (tensorLastUnit p ((Middle.transpose M).obj a)).app z := rfl

/-- The output-action unitor of an actual composite, including its full
strong-transformation naturality, is the last-factor lift of the original one. -/
theorem middleComposite_mapId_eq_lastLift (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})) (b : B) :
    ((middleComposite M N).mapId ⟨b⟩).hom = lastLiftUnit (N.mapId ⟨b⟩).hom M := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro a
  change (_ ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- The last-factor rebracketing square commutes with the actual units. -/
theorem lastAssociator_identity :
    RespectsEndpointIdentity (eqToIso (last_naturality X M t))
      (tensorLastUnit p (leftInner X M)) (tensorLastUnit (lastLiftUnit p M) X) := by
  intro z
  change (eqToHom (last_naturality X M t)).app z ≫
    (tensorLastUnit (lastLiftUnit p M) X).app ((associate X M Y).obj z) =
      (associate X M Y).map ((tensorLastUnit p (leftInner X M)).app z)
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp, tensorLastUnit_app, tensorLastUnit_app, last_cell_app]
  rw [Second.cell_app, Second.cell_app]
  congr 2
  rw [lastLiftUnit_app, tensorLastUnit_app]
  rfl

/-- Full factor interchange respects the original last-factor unit. -/
theorem factorOrder_last_identity {X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (s : X ⟶ X') :
    RespectsEndpointIdentity (eqToIso (factor_order s t).symm)
      (tensorLastUnit p X) (tensorLastUnit p X') := by
  intro z
  change (eqToHom (factor_order s t).symm).app z ≫
    (tensorLastUnit p X').app ((mapFirst s).obj z) = (mapFirst s).map ((tensorLastUnit p X).app z)
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp, tensorLastUnit_app, tensorLastUnit_app, Second.cell_app, Second.cell_app, First.on_native, Functor.map_id]
  rfl

theorem identifyFirst_last_identity {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (h : F = F') :
    RespectsEndpointIdentity (eqToIso (identifyFirst_last t h)) (tensorLastUnit p F) (tensorLastUnit p F') := by
  subst F'
  intro z
  change (eqToHom (identifyFirst_last t rfl)).app z ≫ _ = _
  rw [eqToHom_app]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The actual last-factor comparison of the expose-middle equivalence
satisfies the identity-action equation. -/
theorem exposeMiddleOutput_identity
    (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN})) :
    RespectsEndpointIdentity (exposeMiddleOutput X M N t)
      (tensorLastUnit (lastLiftUnit p N) (leftInner X M))
      (tensorLastUnit p (leftInner X (middleComposite M N))) :=
  pasteEndpointIdentity
    (reverseEndpointIdentity (associator (leftInner X M) N Y) (lastAssociator_identity p (leftInner X M) N))
    (factorOrder_last_identity p (leftInner (leftInner X M) N) (outerAssociator X M N))

/-- The complete original crossing, including both bracket changes,
commutes with the supplied identity-action cells. -/
theorem crossMiddleOutput_identity
    (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
    (s : middleComposite N M ⟶ middleComposite M N) :
    RespectsEndpointIdentity (crossMiddleOutput X M N t s)
      (tensorLastUnit (lastLiftUnit p M) (leftInner X N))
      (tensorLastUnit (lastLiftUnit p N) (leftInner X M)) :=
  pasteEndpointIdentity (exposeMiddleOutput_identity p X N M)
    (pasteEndpointIdentity (factorOrder_last_identity p (leftInner X (middleComposite N M)) (liftCrossing X M N s))
      (reverseEndpointIdentity (exposeMiddle X M N Y) (exposeMiddleOutput_identity p X M N)))

end TensorUnit

section ContractionIdentity
universe v u vY uY vX uX
variable {B : Type u} [Category.{v} B]
variable {F X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable {P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})}
variable (r : F ⟶ X) (n : P ⟶ Q) (b : B)

/-- Contracting both factors respects two unit cells whenever the second
contraction's native square commutes with those cells. -/
theorem contractChangeLast_identity_of {G Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} {t : G ⟶ G}
    {t' : Y ⟶ Y} {c : G ⟶ Y} (e : t ≫ c ≅ c ≫ t') (p : t ⟶ 𝟙 G) (q : t' ⟶ 𝟙 Y)
    (h : ∀ (i : B) (y : G.obj ⟨op i⟩),
      (e.hom.as.app ⟨op i⟩).toNatTrans.app y ≫ (q.as.app ⟨op i⟩).toNatTrans.app ((Second.part c i).obj y) =
      (Second.part c i).map ((p.as.app ⟨op i⟩).toNatTrans.app y)) :
    RespectsEndpointIdentity (F := mapBoth r c) (contractChangeLast r t t' c c e)
      (tensorLastUnit p F) (tensorLastUnit q X) := by
  intro z
  rw [contractChangeLast_app, tensorLastUnit_app, tensorLastUnit_app, Second.cell_app, Second.cell_app,
    mapBoth_native, Functor.map_id]
  let J := CategoryTheory.Prod.sectR ((First.part r z.as.mid).obj z.as.first) (Y.obj ⟨op z.as.mid⟩) ⋙
    (insertion X Y z.as.mid)
  exact (J.map_comp _ _).symm.trans (congrArg J.map (h z.as.mid z.as.second))

/-- The unitor of the covariant module action, with its sources explicit. -/
def covariantUnitCell (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}))
    (b : LocallyDiscrete B) : P.map (𝟙 b) ⟶ 𝟙 (P.obj b) :=
  (P.mapId b).hom

set_option maxHeartbeats 350000 in
theorem contractChangeLast_identity :
    let b' : LocallyDiscrete B := ⟨b⟩
    let t := P.map (𝟙 b')
    let t' := Q.map (𝟙 b')
    let c := n.app b'
    let e : t ≫ c ≅ c ≫ t' := n.naturality (𝟙 b')
    let pu := covariantUnitCell P b'
    let qu := covariantUnitCell Q b'
    RespectsEndpointIdentity (F := mapBoth r c) (contractChangeLast r t t' c c e)
      (tensorLastUnit pu F) (tensorLastUnit qu X) := by
  dsimp only
  apply contractChangeLast_identity_of
  intro i y
  let n' := Second.part (n.app ⟨b⟩) i
  let coord {W Z : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} {h k : W ⟶ Z}
      (e : h ⟶ k) (y : W.obj ⟨op i⟩) := (e.as.app ⟨op i⟩).toNatTrans.app y
  have h := congrArg (fun e => (e.as.app ⟨op i⟩).toNatTrans.app y) (n.naturality_id ⟨b⟩)
  change coord (n.naturality (𝟙 ⟨b⟩)).hom y ≫ coord (Q.mapId ⟨b⟩).hom (n'.obj y) =
    n'.map (coord (P.mapId ⟨b⟩).hom y) ≫ 𝟙 _ ≫ 𝟙 _ at h
  simpa only [covariantUnitCell, Category.comp_id] using h

end ContractionIdentity

section MixedIdentity
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- The unit of the covariant action evaluated in the actual input fibre. -/
def covariantUnitAt.{w,k} (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k}))
    (a b : B) : ((P.map (𝟙 ⟨b⟩)).app ⟨op a⟩).toFunctor ⟶ 𝟭 ((P.obj ⟨b⟩).obj ⟨op a⟩) :=
  ((covariantUnitCell P ⟨b⟩).as.app ⟨op a⟩).toNatTrans

/-- The actual mixed contraction stage at the identity respects the unitors
obtained from the transition of the second module. -/
theorem mixedContractionOutput_identity
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) (a b : B) :
    let d : LocallyDiscrete B := ⟨b⟩
    let q := covariantUnitCell N d
    RespectsEndpointIdentity (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a (𝟙 b))
      (tensorLastUnit (lastLiftUnit q N) (leftInner (row M a) M)) (tensorLastUnit q (row M a)) := by
  dsimp only
  have h := contractChangeLast_identity (rowMultiplication.{v,u,vM,uM} M m a) n b
  dsimp only [covariantUnitCell] at h ⊢
  rw [middleComposite_mapId_eq_lastLift N N b] at h
  exact h

/-- Evaluate the genuine composite unitor as a second-factor tensor action. -/
theorem covariantUnitAt_composite.{vB,uB,vP,uP,vQ,uQ} {D : Type uB} [Category.{vB} D]
    (P : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vP,uP}))
    (Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vQ,uQ})) (a b : D) :
    covariantUnitAt (middleComposite P Q) a b = tensorLastUnit (covariantUnitCell Q ⟨b⟩) (row P a) := by
  unfold covariantUnitAt covariantUnitCell
  rw [middleComposite_mapId_eq_lastLift P Q b]
  rfl

set_option maxHeartbeats 420000 in
/-- The original mixed multiplication's covariant endpoint square at the identity
commutes with the actual action unitors of H⊙H and H (H = M⊙N). -/
theorem mixedMultiplicationOutput_identity
    (s : middleComposite N M ⟶ middleComposite M N) (m : middleComposite M M ⟶ M)
    (n : middleComposite N N ⟶ N) (a b : B) :
    let H := middleComposite M N
    let HH := middleComposite H H
    let μ := mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a b
    let σ := mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a (𝟙 b)
    RespectsEndpointIdentity (F := μ) σ (covariantUnitAt HH a b) (covariantUnitAt H a b) := by
  dsimp only
  let H := middleComposite M N
  let d : LocallyDiscrete B := ⟨b⟩
  let p := covariantUnitCell N d
  have hq : covariantUnitCell H d = lastLiftUnit p M := middleComposite_mapId_eq_lastLift M N b
  rw [covariantUnitAt_composite H H a b, covariantUnitAt_composite M N a b, hq]
  exact pasteEndpointIdentity (identifyFirst_last_identity (lastLiftUnit p M) (middleRow M N a))
    (pasteEndpointIdentity (crossMiddleOutput_identity p (row M a) M N s)
      (mixedContractionOutput_identity M N m n a b))

end MixedIdentity
end ContextualComposition.RelativeTensor.Iterated
