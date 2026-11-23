module
public import ContextualComposition.RelativeTensorMixedUnitOutput
public import ContextualComposition.RelativeTensorMixedOutputComposition
public import ContextualComposition.RelativeTensorIndexedRightUnitor
public import ContextualComposition.RelativeTensorCrossingPayload
public import ContextualComposition.RelativeTensorMixedBundlingInterfaces

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section UnitIdentity
universe v u
variable {B : Type u} [Category.{v} B]
variable {P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v})}
variable (j : unitModule B ⟶ P)

/-- Chosen output unit cell in the original fixed row of a module. -/
def rowOutputId.{w,k} {T : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k})} (a b : B) : forward (row T a) (𝟙 b) ⟶ 𝟭 ((column T b).obj ⟨op a⟩) :=
  ((T.mapId ⟨b⟩).hom.as.app ⟨op a⟩).toNatTrans

theorem unitOutputFirst_identity {a b : B} (p : a ⟶ b) :
    (mixedUnitOutputFirst P j (𝟙 b) p).hom ≫ (rowOutputId (T := P) a b).app (nativeUnitValue j p) =
      ((j.app ⟨b⟩).app ⟨op a⟩).toFunctor.map ((rowOutputId (T := unitModule B) a b).app (Discrete.mk p)) := by
  have h := congrArg (fun e => (e.as.app ⟨op a⟩).toNatTrans.app (Discrete.mk p)) (j.naturality_id ⟨b⟩)
  change (mixedUnitOutputFirst P j (𝟙 b) p).hom ≫ (rowOutputId (T := P) a b).app (nativeUnitValue j p) =
      ((j.app ⟨b⟩).app ⟨op a⟩).toFunctor.map ((rowOutputId (T := unitModule B) a b).app (Discrete.mk p)) ≫ 𝟙 _ ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

theorem unitOutputSecond_identity (b : B) :
    (mixedUnitOutputSecond P j (𝟙 b)).hom ≫ (rowOutputId (T := P) b b).app (nativeUnitValue j (𝟙 b)) =
      ((column P b).mapId ⟨op b⟩).hom.toNatTrans.app (nativeUnitValue j (𝟙 b)) := by
  let z := Discrete.mk (𝟙 b)
  let A := ((j.app ⟨b⟩).app ⟨op b⟩).toFunctor
  let I := (Cat.Hom.toNatIso ((j.app ⟨b⟩).naturality (𝟙 (⟨op b⟩ : LocallyDiscrete Bᵒᵖ)))).app z
  let K := (Cat.Hom.toNatIso ((column (unitModule B) b).mapId ⟨op b⟩)).app z
  let L := (Cat.Hom.toNatIso ((row (unitModule B) b).mapId ⟨b⟩)).app z
  let Q := (Cat.Hom.toNatIso ((column P b).mapId ⟨op b⟩)).app (A.obj z)
  let e : ((backward (column (unitModule B) b) (𝟙 b)).obj z) =
      (forward (row (unitModule B) b) (𝟙 b)).obj z := Discrete.ext
        ((Category.comp_id (𝟙 b)).trans (Category.id_comp (𝟙 b)).symm)
  have hin : I.hom ≫ Q.hom = A.map K.hom := by
    have h := congrArg (fun k => (Cat.Hom₂.toNatTrans k).app z) ((j.app ⟨b⟩).naturality_id ⟨op b⟩)
    change I.hom ≫ Q.hom = A.map K.hom ≫ 𝟙 _ ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  have hout := unitOutputFirst_identity j (𝟙 b)
  have hc : eqToHom (congrArg A.obj e) ≫ A.map L.hom = A.map K.hom := by
    rw [← eqToHom_map A e, ← A.map_comp]
    exact congrArg A.map (Discrete.hom_eq : eqToHom e ≫ L.hom = K.hom)
  change (I.inv ≫ eqToHom (congrArg A.obj e) ≫ (mixedUnitOutputFirst P j (𝟙 b) (𝟙 b)).hom) ≫
    (rowOutputId (T := P) b b).app (A.obj z) = Q.hom
  simp only [Category.assoc]
  rw [hout]
  change I.inv ≫ (eqToHom (congrArg A.obj e) ≫ A.map L.hom) = Q.hom
  rw [hc, ← hin]
  exact I.inv_hom_id_assoc Q.hom


section TensorIdentity
universe vX uX vY uY
variable (F : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- Inverting the designated identity balance inserts the covariant unitor
and the inverse contravariant unitor on the original tensor. -/
theorem inverseIdentityBalance (b : B) (x : F.obj ⟨b⟩) (y : G.obj ⟨op b⟩) :
    (balancing F G (𝟙 b) x y).inv = (insertion F G b).map
      (productMap ((F.mapId ⟨b⟩).hom.toNatTrans.app x) ((G.mapId ⟨op b⟩).inv.toNatTrans.app y)) := by
  let i := (insertion F G b).mapIso
    (((Cat.Hom.toNatIso (F.mapId ⟨b⟩)).app x).symm.prod ((Cat.Hom.toNatIso (G.mapId ⟨op b⟩)).app y))
  have e : balancing F G (𝟙 b) x y = i := Iso.ext (by
    have h := (restrict (𝟭 (Tensor F G))).unit x y
    change (balancing F G (𝟙 b) x y).hom = (insertion F G b).map
      (productMap ((F.mapId ⟨b⟩).inv.toNatTrans.app x) ((G.mapId ⟨op b⟩).hom.toNatTrans.app y)) at h
    exact h)
  exact congrArg Iso.inv e

end TensorIdentity

section Mixed
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)

theorem mixedUnitAt_map {a b : B} {p q : Discrete (a ⟶ b)} (f : p ⟶ q) :
    (mixedUnitAt M N jM jN a b).map f = (insertion (row M a) (column N b) b).map
      (productMap (((jM.app ⟨b⟩).app ⟨op a⟩).toFunctor.map f) (𝟙 (nativeUnitValue jN (𝟙 b)))) := by
  change (mapBoth (rowMap jM a) (jN.app ⟨b⟩)).map
      ((insertion (row (unitModule B) a) (column (unitModule B) b) b).map
        (productMap f (𝟙 (Discrete.mk (𝟙 b))))) = _
  rw [mapBoth_native, Functor.map_id]
  rfl

set_option maxHeartbeats 450000 in
/-- The original output comparison at the identity respects both chosen unitors. -/
theorem mixedUnitOutput_identity (a b : B) :
    RespectsEndpointIdentity (mixedUnitOutput M N jM jN (a := a) (𝟙 b))
      (rowOutputId (T := unitModule B) a b) (rowOutputId (T := middleComposite M N) a b) := by
  intro p
  let x := nativeUnitValue jM p.as
  let y := nativeUnitValue jN (𝟙 b)
  let J := insertion (row M a) (column N b) b
  have target :
      (rowOutputId (T := middleComposite M N) a b).app ((mixedUnitAt M N jM jN a b).obj p) =
        J.map (productMap (𝟙 x) ((rowOutputId (T := N) b b).app y)) := by
    change (covariantUnitAt (middleComposite M N) a b).app ((mixedUnitAt M N jM jN a b).obj p) = _
    rw [covariantUnitAt_composite, tensorLastUnit_app, Second.cell_app]
    rfl
  rw [mixedUnitOutput_app, target, inverseIdentityBalance, mixedUnitAt_map]
  change (J.map _ ≫ J.map _ ≫ J.map _) ≫ J.map _ = J.map _
  simp only [Category.assoc, ← J.map_comp]
  apply congrArg J.map
  apply Prod.ext
  · change (mixedUnitOutputFirst M jM (𝟙 b) p.as).hom ≫
      ((row M a).mapId ⟨b⟩).hom.toNatTrans.app x ≫ 𝟙 _ ≫ 𝟙 _ = _
    have hrow : ((row M a).mapId ⟨b⟩).hom.toNatTrans.app x = (rowOutputId (T := M) a b).app x :=
      Category.comp_id _
    rw [hrow]
    simp only [Category.comp_id]
    exact unitOutputFirst_identity jM p.as
  · change 𝟙 _ ≫ ((column N b).mapId ⟨op b⟩).inv.toNatTrans.app y ≫
      (mixedUnitOutputSecond N jN (𝟙 b)).hom ≫ (rowOutputId (T := N) b b).app y = 𝟙 _
    rw [Category.id_comp, unitOutputSecond_identity jN b]
    exact Iso.inv_hom_id_app (Cat.Hom.toNatIso ((column N b).mapId ⟨op b⟩)) y

end Mixed
end UnitIdentity

section UnitComposition
universe v u
variable {B : Type u} [Category.{v} B]

section PureSection
variable (a : B)
local notation "X" => row (unitModule B) a
local notation "I" => unitModule B

/-- The output comparison of the right-unit splitting of a pure label,
using the designated inverse balance followed by the discrete label cast. -/
def pureUnitSectionOutput {b c : B} (g : b ⟶ c) :
    forward X g ⋙ RightUnit.sectionFunctor c X ≅
      RightUnit.sectionFunctor b X ⋙ ((leftInner X I).map g.toLoc).toFunctor :=
  Discrete.natIso fun p =>
    (balancing X (column I c) g p (Discrete.mk (𝟙 c))).symm ≪≫
      (insertion X (column I c) b).mapIso ((Iso.refl p).prod
        (eqToIso (Discrete.ext ((Category.comp_id g).trans (Category.id_comp g).symm))))

set_option maxHeartbeats 300000 in
/-- The literal pure splitting comparison is the chosen-equivalence mate.
Faithfulness of right-unit evaluation reduces the equality to discreteness of the hom fibre. -/
theorem pureUnitSectionOutput_mate {b c : B} (g : b ⟶ c) :
    pureUnitSectionOutput a g =
      reverseInputSquare (RightUnit.equivalence b X) (RightUnit.equivalence c X) (RightUnit.indexedBase X g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext z
  let e := RightUnit.equivalence c X
  apply e.functor.map_injective
  exact Discrete.hom_eq (α := a ⟶ c)

set_option maxHeartbeats 300000 in
theorem pureUnitSectionOutput_composition {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    RespectsEndpointComposition (pureUnitSectionOutput a f) (pureUnitSectionOutput a g)
      (pureUnitSectionOutput a (f ≫ g))
      ((X).mapComp f.toLoc g.toLoc).hom.toNatTrans
      ((leftInner X I).mapComp f.toLoc g.toLoc).hom.toNatTrans := by
  rw [pureUnitSectionOutput_mate, pureUnitSectionOutput_mate, pureUnitSectionOutput_mate]
  exact reverseEndpointComposition (RightUnit.equivalence b X) (RightUnit.equivalence c X)
    (RightUnit.equivalence d X) (RightUnit.base_comp X f g)
end PureSection

section InverseBalances
universe vX uX vY uY
variable {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
variable {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}

theorem firstMap_inverseBalance (s : F ⟶ F') {b c : B} (g : b ⟶ c)
    (x : F.obj ⟨b⟩) (y : G.obj ⟨op c⟩) :
    (mapFirst (G := G) s).map (balancing F G g x y).inv =
      (insertion F' G c).map (productMap (First.port s g x).inv (𝟙 y)) ≫
      (balancing F' G g ((First.part s b).obj x) y).inv := by
  let E := (balancing F' G g ((First.part s b).obj x) y) ≪≫
    (insertion F' G c).mapIso ((First.port s g x).prod (Iso.refl y))
  have h : (mapFirst (G := G) s).mapIso (balancing F G g x y) = E :=
    Iso.ext (First.on_balance s g x y)
  exact congrArg Iso.inv h

theorem secondMap_inverseBalance (s : G ⟶ G') {b c : B} (g : b ⟶ c)
    (x : F.obj ⟨b⟩) (y : G.obj ⟨op c⟩) :
    (mapSecond (F := F) s).map (balancing F G g x y).inv =
      (balancing F G' g x ((Second.part s c).obj y)).inv ≫
      (insertion F G' b).map (productMap (𝟙 x) (Second.port s g y).inv) := by
  let E := (insertion F G' b).mapIso ((Iso.refl x).prod (Second.port s g y)) ≪≫
    (balancing F G' g x ((Second.part s c).obj y))
  have h : (mapSecond (F := F) s).mapIso (balancing F G g x y) = E :=
    Iso.ext (Second.on_balance s g x y)
  exact congrArg Iso.inv h
end InverseBalances

section Stages
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable (a : B)
local notation "X" => row (unitModule B) a
local notation "R" => row M a
local notation "I" => unitModule B

private def firstUnitPayload := firstMap (rowMap jM a) I
private def secondUnitPayload := crossingPayload R jN

private theorem firstUnitPayload_port {b c : B} (g : b ⟶ c) (z : Tensor X (column I b)) :
    ((firstUnitPayload M jM a).naturality g.toLoc).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (factor_order (rowMap jM a) ((I).map g.toLoc)).symm).app z = _
  rw [eqToHom_app]; rfl

private theorem catStrong_composition {T : Type*} [Bicategory T] {F G : T ⥤ᵖ Cat}
    (η : F ⟶ G) {b c d : T} (f : b ⟶ c) (g : c ⟶ d) :
    RespectsEndpointComposition (Cat.Hom.toNatIso (η.naturality f))
      (Cat.Hom.toNatIso (η.naturality g)) (Cat.Hom.toNatIso (η.naturality (f ≫ g)))
      (F.mapComp f g).hom.toNatTrans (G.mapComp f g).hom.toNatTrans := by
  intro z
  have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans (η.naturality_comp f g)) z
  change _ = _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ at h
  simp only [Category.id_comp, Category.comp_id] at h
  exact h

private def stageOutput {b c : B} (t : b ⟶ c) :=
  pasteInputSquare (pureUnitSectionOutput a t)
    (pasteInputSquare (Cat.Hom.toNatIso ((firstUnitPayload M jM a).naturality t.toLoc))
      (Cat.Hom.toNatIso ((secondUnitPayload M N jN a).naturality t.toLoc)))

private theorem stageOutput_composition {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    RespectsEndpointComposition (stageOutput M N jM jN a f) (stageOutput M N jM jN a g)
      (stageOutput M N jM jN a (f ≫ g))
      ((X).mapComp f.toLoc g.toLoc).hom.toNatTrans
      ((leftInner R N).mapComp f.toLoc g.toLoc).hom.toNatTrans := by
  exact pasteEndpointComposition (pureUnitSectionOutput_composition a f g)
    (pasteEndpointComposition (catStrong_composition (firstUnitPayload M jM a) f.toLoc g.toLoc)
      (catStrong_composition (secondUnitPayload M N jN a) f.toLoc g.toLoc))


set_option maxHeartbeats 500000 in
private theorem stageOutput_eq {b c : B} (g : b ⟶ c) :
    stageOutput M N jM jN a g = mixedUnitOutput M N jM jN (a := a) g := by
  apply Iso.ext
  apply NatTrans.ext
  funext p
  let P := mapFirst (G := column I c) (rowMap jM a)
  let Q := mapSecond (F := R) (jN.app ⟨c⟩)
  let e : Discrete.mk (g ≫ 𝟙 c) = Discrete.mk (𝟙 b ≫ g) :=
    Discrete.ext ((Category.comp_id g).trans (Category.id_comp g).symm)
  let l := (insertion X (column I c) b).map (productMap (𝟙 p) (eqToHom e))
  let v := (balancing X (column I c) g p (Discrete.mk (𝟙 c))).inv
  let z := (RightUnit.sectionFunctor b X).obj p
  let q := (mapFirst (G := column I b) (rowMap jM a)).obj z
  change (Q.map (P.map (v ≫ l)) ≫
      (Q.map (((firstUnitPayload M jM a).naturality g.toLoc).hom.toNatTrans.app z) ≫
        ((secondUnitPayload M N jN a).naturality g.toLoc).hom.toNatTrans.app q)) = _
  rw [firstUnitPayload_port]
  erw [Functor.map_id]
  refine (congrArg (fun t => Q.map (P.map (v ≫ l)) ≫ t) (Category.id_comp _)).trans ?_
  change (Q.map (P.map (v ≫ l)) ≫ (crossingSquare R jN g.toLoc).hom.toNatTrans.app q) = _
  rw [mixedUnitOutput_app, crossingSquare_app]
  dsimp only [P, Q, v, l]
  rw [Functor.map_comp, Functor.map_comp, firstMap_inverseBalance, Functor.map_comp,
    Second.on_native, secondMap_inverseBalance, First.on_native, Second.on_native, Functor.map_id, Functor.map_id]
  let J := insertion R (column N c) b
  simp only [Category.assoc]
  change _ ≫ _ ≫ J.map (productMap _ _) ≫ J.map (productMap _ _) ≫ J.map (productMap _ _) = _
  have he : (Second.part (jN.app ⟨c⟩) b).map (eqToHom e) =
      eqToHom (congrArg (fun p : b ⟶ c => nativeUnitValue jN p)
        ((Category.comp_id g).trans (Category.id_comp g).symm)) := eqToHom_map _ _
  rw [he]
  simp only [← J.map_comp]
  congr 2
  apply congrArg J.map
  apply Prod.ext
  · change 𝟙 (nativeUnitValue jM p.as) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.id_comp, Category.id_comp]
  · rfl


set_option maxHeartbeats 450000 in
/-- The given comparison respects the actual covariant compositors at fixed input. -/
theorem mixedUnitOutput_composition {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    RespectsEndpointComposition (mixedUnitOutput M N jM jN (a := a) f)
      (mixedUnitOutput M N jM jN (a := a) g) (mixedUnitOutput M N jM jN (a := a) (f ≫ g))
      (((X).mapComp f.toLoc g.toLoc).hom.toNatTrans)
      (covariantCompAt (middleComposite M N) a f g) := by
  have h : covariantCompAt (middleComposite M N) a f g =
      ((leftInner R N).mapComp f.toLoc g.toLoc).hom.toNatTrans := by
    rw [covariantCompAt_composite]
    rfl
  rw [h, ← stageOutput_eq, ← stageOutput_eq, ← stageOutput_eq]
  exact stageOutput_composition M N jM jN a f g

end Stages
end UnitComposition

section BundledRow
universe v u
variable {B : Type u} [Category.{v} B]

private theorem rowOutputId_eval.{w,k}
    (T : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k})) (a b : B) :
    ((row T a).mapId ⟨b⟩).hom.toNatTrans = rowOutputId (T := T) a b := by
  apply NatTrans.ext
  funext x
  exact Category.comp_id _

private theorem rowOutputComp_eval.{w,k}
    (T : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k})) (a : B)
    {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    ((row T a).mapComp f.toLoc g.toLoc).hom.toNatTrans = covariantCompAt T a f g := by
  apply NatTrans.ext
  funext x
  exact Category.comp_id _

section CommonLevels
variable {C : Type u} [Category.{max u v} C]
variable (M N : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule C ⟶ M) (jN : unitModule C ⟶ N)
variable (a : C)

set_option maxHeartbeats 400000 in
/-- The original mixed unit as a strong map in the covariant endpoint,
with the input fixed at common native Cat levels. This does not yet assert joint compatibility. -/
def mixedUnitOutputRow : row (unitModule C) a ⟶ row (middleComposite M N) a :=
  strongCatFromEndpointLaws
    (fun b => mixedUnitAt M N jM jN a b.as)
    (fun f => mixedUnitOutput M N jM jN (a := a) f.as)
    (fun b => by
      rw [rowOutputId_eval, rowOutputId_eval]
      exact mixedUnitOutput_identity M N jM jN a b.as)
    (fun f g => by
      erw [rowOutputComp_eval (middleComposite M N) a f.as g.as]
      exact mixedUnitOutput_composition M N jM jN a f.as g.as)

theorem mixedUnitOutputRow_app (b : C) :
    HEq ((mixedUnitOutputRow M N jM jN a).app ⟨b⟩).toFunctor (mixedUnitAt M N jM jN a b) := by
  rfl

theorem mixedUnitOutputRow_naturality {b c : C} (g : b ⟶ c) :
    Cat.Hom.toNatIso ((mixedUnitOutputRow M N jM jN a).naturality g.toLoc) =
      mixedUnitOutput M N jM jN (a := a) g := rfl

end CommonLevels
end BundledRow

end ContextualComposition.RelativeTensor.Iterated
